import CertiKOS.VEPT

/-!
# Virtualization: the VMCS, ported from the Coq version

Transcribed from `coq/VMCS.v`, which ports mCertiKOS's `objects/ObjVMCS.v`.

The VMCS is the processor's record of a virtual machine. On real hardware it
is accessed with `vmread` and `vmwrite`; here it is a block of the kernel
region at `vb`: the revision id at `vb`, the abort indicator at `vb + 1`,
field `enc` at `vb + 2 + enc`. `vmread` and `vmwrite` are a read and a
write there, inside the critical section.

* `MatchV`: the block holds every field that is known.
* `vmread_step`, `vmwrite_step`: the two hardware accesses as steps.
* `readz_step`, `writez_step`, `readz64_step`, `writez64_step`,
  `setIntwin_step`, `setDesc_step`, `injectEvent_step`,
  `checkPending_step`, `checkIntShadow_step`, `exitReason_step`,
  `exitFaultAddr_step`: **each function refines its specification.**

What differs from `coq/VMCS.v`: fields are machine words (`Val`). The
revision id, the abort indicator and the TSC offset accessors are not
transcribed (the last two are `readz64` and `writez64` at one encoding).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace VVMCS

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MPTIntro
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Abstract data -/

structure VMCS where
  revid : Option Val
  abrtid : Option Val
  data : Nat → Option Val

structure VSt where
  ikern : Bool
  pg : Bool
  ihost : Bool
  vmcs : VMCS

/-- The field encodings (`vmcs_ZtoEncoding` is defined exactly on these). -/
def encodings : List Nat := [0, 2048, 2050, 2052, 2054, 2056, 2058, 2060, 2062, 3072, 3074, 3076, 3078, 3080, 3082, 3084, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8200, 8202, 8204, 8208, 8210, 8212, 8218, 8219, 9216, 10240, 10242, 10244, 10246, 10248, 10250, 10252, 10254, 10256, 11264, 11266, 11268, 16384, 16386, 16388, 16390, 16392, 16394, 16396, 16398, 16400, 16402, 16404, 16406, 16408, 16410, 16412, 16414, 16416, 16418, 17408, 17410, 17412, 17414, 17416, 17418, 17420, 17422, 18432, 18434, 18436, 18438, 18440, 18442, 18444, 18446, 18448, 18450, 18452, 18454, 18456, 18458, 18460, 18462, 18464, 18466, 18468, 18470, 18472, 18474, 18478, 19456, 24576, 24578, 24580, 24582, 24584, 24586, 24588, 24590, 25600, 25602, 25604, 25606, 25608, 25610, 26624, 26626, 26628, 26630, 26632, 26634, 26636, 26638, 26640, 26642, 26644, 26646, 26648, 26650, 26652, 26654, 26656, 26658, 26660, 26662, 27648, 27650, 27652, 27654, 27656, 27658, 27660, 27662, 27664, 27666, 27668, 27670]

def valid_enc (z : Nat) : Bool := encodings.contains z

theorem valid_enc_lt {z : Nat} (h : valid_enc z = true) : z ≤ 27670 := by
  unfold valid_enc at h
  have hm : z ∈ encodings := List.elem_iff.mp h
  have hall : encodings.all (· ≤ 27670) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall z hm)

def C_VMCS_PRI_PROC_BASED_CTLS : Nat := 16386
def C_VMCS_ENTRY_INTR_INFO : Nat := 16406
def C_VMCS_ENTRY_EXCEPTION_ERROR : Nat := 16408
def C_VMCS_EXIT_REASON : Nat := 17410
def C_VMCS_GUEST_INTERRUPTIBILITY : Nat := 18468
def C_VMCS_GUEST_PHYSICAL_ADDRESS : Nat := 9216
def VALID : Val := 2147483648
def NOT_INTWIN : Val := 4294967291

/-- `seg_encode`: base, limit, access rights, selector. GDTR and IDTR (8, 9)
have only a base and a limit. -/
def seg_table : List (Nat × (Nat × Nat × Nat × Nat)) :=
  [(0, (26632, 18434, 18454, 2050)), (1, (26636, 18438, 18458, 2054)), (2, (26630, 18432, 18452, 2048)),
   (3, (26638, 18440, 18460, 2056)), (4, (26640, 18442, 18462, 2058)), (5, (26634, 18436, 18456, 2052)),
   (6, (26642, 18444, 18464, 2060)), (7, (26644, 18446, 18466, 2062)), (8, (26646, 18448, 0, 0)),
   (9, (26648, 18450, 0, 0))]

def lookup : List (Nat × (Nat × Nat × Nat × Nat)) → Nat → Option (Nat × Nat × Nat × Nat)
  | [], _ => none
  | (k, p) :: t, x => if x = k then some p else lookup t x

/-! ## Specifications (`ObjVMCS.v`) -/

def flags (d : VSt) : Prop := d.ikern = true ∧ d.pg = true ∧ d.ihost = true

instance (d : VSt) : Decidable (flags d) := by unfold flags; exact inferInstance

def setData (d : VSt) (dt : Nat → Option Val) : VSt :=
  { d with vmcs := { d.vmcs with data := dt } }

def vmcs_readz_spec (enc : Nat) (d : VSt) : Option Val :=
  if flags d ∧ valid_enc enc = true then d.vmcs.data enc else none

def vmcs_writez_spec (enc value : Nat) (d : VSt) : Option VSt :=
  if flags d ∧ valid_enc enc = true then some (setData d (setAt d.vmcs.data enc (some (BitVec.ofNat 32 value))))
  else none

/-- `vmcs_readz64_spec`: the two words, low at `enc`, high at `enc + 1`. -/
def vmcs_readz64_spec (enc : Nat) (d : VSt) : Option (Val × Val) :=
  if flags d ∧ valid_enc enc = true then
    match d.vmcs.data enc, d.vmcs.data (enc + 1) with
    | some lo, some hi => some (lo, hi)
    | _, _ => none
  else none

/-- `write64_aux`: the low word at `enc`, the high word at `enc + 1`. -/
def write64 (enc : Nat) (lo hi : Val) (dt : Nat → Option Val) : Nat → Option Val :=
  setAt (setAt dt enc (some lo)) (enc + 1) (some hi)

def vmcs_writez64_spec (enc : Nat) (lo hi : Val) (d : VSt) : Option VSt :=
  if flags d ∧ valid_enc enc = true then some (setData d (write64 enc lo hi d.vmcs.data)) else none

def vmx_set_intercept_intwin_spec (enable : Nat) (d : VSt) : Option VSt :=
  if flags d then
    match d.vmcs.data C_VMCS_PRI_PROC_BASED_CTLS with
    | some c =>
      if enable = 1 then some (setData d (setAt d.vmcs.data C_VMCS_PRI_PROC_BASED_CTLS (some (c ||| 4))))
      else some (setData d (setAt d.vmcs.data C_VMCS_PRI_PROC_BASED_CTLS (some (c &&& NOT_INTWIN))))
    | none => none
  else none

def vmx_set_desc_aux (seg : Nat) (sel base lim ar : Val) (dt : Nat → Option Val) : Option (Nat → Option Val) :=
  match lookup seg_table seg with
  | some (eb, el, ea, es) =>
    if seg < 8 then some (setAt (setAt (setAt (setAt dt eb (some base)) el (some lim)) ea (some ar)) es (some sel))
    else some (setAt (setAt dt eb (some base)) el (some lim))
  | none => none

def vmx_set_desc_spec (seg : Nat) (sel base lim ar : Val) (d : VSt) : Option VSt :=
  if flags d then
    match vmx_set_desc_aux seg sel base lim ar d.vmcs.data with
    | some dt => some (setData d dt)
    | none => none
  else none

def vmx_inject_event_spec (type vector errcode : Val) (ev : Nat) (d : VSt) : Option VSt :=
  if flags d then
    match d.vmcs.data C_VMCS_ENTRY_INTR_INFO with
    | some i =>
      if i &&& VALID = 0 then
        let i2 := (VALID ||| type) ||| vector
        if ev = 1 then
          some (setData d (setAt (setAt d.vmcs.data C_VMCS_ENTRY_INTR_INFO (some (i2 ||| 2048)))
            C_VMCS_ENTRY_EXCEPTION_ERROR (some errcode)))
        else some (setData d (setAt d.vmcs.data C_VMCS_ENTRY_INTR_INFO (some i2)))
      else some d
    | none => none
  else none

def testBit (enc : Nat) (mask : Val) (d : VSt) : Option Val :=
  if flags d then
    match d.vmcs.data enc with
    | some c => if c &&& mask = 0 then some 0 else some 1
    | none => none
  else none

def vmx_check_pending_event_spec := testBit C_VMCS_ENTRY_INTR_INFO VALID
def vmx_check_int_shadow_spec := testBit C_VMCS_GUEST_INTERRUPTIBILITY 3

def vmx_get_exit_reason_spec (d : VSt) : Option Val :=
  if flags d then
    match d.vmcs.data C_VMCS_EXIT_REASON with
    | some r => some (r &&& 65535)
    | none => none
  else none

def vmx_get_exit_fault_addr_spec (d : VSt) : Option Val :=
  if flags d then d.vmcs.data C_VMCS_GUEST_PHYSICAL_ADDRESS else none

/-! ## The VMCS in the region -/

def NENC : Nat := 65537

def MatchV (vb : Nat) (v : VMCS) (b : Region) : Prop :=
  (∀ r, v.revid = some r → b vb = r) ∧ (∀ a, v.abrtid = some a → b (vb + 1) = a) ∧
    ∀ e x, e < NENC → v.data e = some x → b (vb + 2 + e) = x

def MatchS (vb : Nat) (d : VSt) (b : Region) : Prop := MatchV vb d.vmcs b

/-- `vmread(e)`, `vmwrite(e, v)`: the cell of field `e`. -/
def encE (vb : Nat) (e : Expr) : Expr := .bin .add (.const (BitVec.ofNat 32 (vb + 2))) e
def vmreadS (vb : Nat) (x : Ident) (e : Expr) : Stmt APrim := .call x .pull [lkE, encE vb e]
def vmwriteS (vb : Nat) (e v : Expr) : Stmt APrim := .call "_" .push [lkE, encE vb e, v]

theorem eval_enc {vb : Nat} (hvb : vb + 2 + NENC ≤ 2 ^ 32) {σ : Locals} {e : Expr} {k : Nat}
    (he : e.eval σ = BitVec.ofNat 32 k) (hk : k < NENC) : ((encE vb e).eval σ).toNat = vb + 2 + k := by
  show (BitVec.ofNat 32 (vb + 2) + e.eval σ).toNat = _
  rw [he, BitVec.toNat_add, tn (by omega), tn (by unfold NENC at *; omega)]; unfold NENC at *; omega

theorem match_write {vb : Nat} {v : VMCS} {b : Region} {k : Nat} (w : Val) (hM : MatchV vb v b) (hk : k < NENC) :
    MatchV vb { v with data := setAt v.data k (some w) } (setCell b (vb + 2 + k) w) := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun r hr => ?_, fun a ha => ?_, fun e x he hx => ?_⟩
  · rw [sc_ne _ _ (by omega)]; exact h1 r hr
  · rw [sc_ne _ _ (by omega)]; exact h2 a ha
  · have hx' : setAt v.data k (some w) e = some x := hx
    by_cases ee : e = k
    · subst ee; rw [setAt_eq] at hx'; cases hx'; exact sc_eq _ _ _
    · rw [setAt_ne _ _ ee] at hx'; rw [sc_ne _ _ (by omega)]; exact h3 e x he hx'

section Code
variable {vb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MS" => MatchS vb

theorem vmread_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) (x : Ident) (hx : x ≠ "lk") {e : Expr} {σ : Locals} {d : VSt}
    {k : Nat} {w : Val} (he : e.eval σ = BitVec.ofNat 32 k) (hk : k < NENC) (hd : d.vmcs.data k = some w) :
    Step εR c i0 MS F (vmreadS vb x e) σ d (σ.set x w) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (encE vb e) (eval_enc hvb he hk)
  rw [hM.2.2 k w hk hd] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem vmwrite_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) (hF : ∀ k, vb + 2 ≤ k → k < vb + 2 + NENC → F k) {e v : Expr}
    {σ : Locals} {d : VSt} {k : Nat} {w : Val} (he : e.eval σ = BitVec.ofNat 32 k) (hk : k < NENC)
    (hv : v.eval σ = w) :
    Step εR c i0 MS F (vmwriteS vb e v) σ d (σ.set "_" 0) (setData d (setAt d.vmcs.data k (some w))) := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (encE vb e) v (eval_enc hvb he hk) hv
  exact ⟨l', _, hr, hcs', match_write w hM hk, fun j hj => sc_ne _ _ (fun ee => hj (hF j (by omega) (by omega)))⟩

theorem enc_ok {k : Nat} (h : valid_enc k = true) : k < NENC ∧ k + 1 < NENC := by
  have := valid_enc_lt h; unfold NENC; omega

/-! ### The functions -/

/-- `r = vmread(enc)` -/
def readzS (vb : Nat) : Stmt APrim := vmreadS vb "r" (.var "enc")

theorem readz_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) {σ : Locals} {d : VSt} {enc : Nat} {r : Val}
    (hσ : σ "enc" = BitVec.ofNat 32 enc) (hs : vmcs_readz_spec enc d = some r) :
    Step εR c i0 MS F (readzS vb) σ d (σ.set "r" r) d := by
  unfold vmcs_readz_spec at hs
  by_cases hc : flags d ∧ valid_enc enc = true
  · rw [if_pos hc] at hs; exact vmread_step εR c i0 hvb "r" (by decide) hσ (enc_ok hc.2).1 hs
  · rw [if_neg hc] at hs; cases hs

/-- `vmwrite(enc, value)` -/
def writezS (vb : Nat) : Stmt APrim := vmwriteS vb (.var "enc") (.var "value")

theorem writez_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) (hF : ∀ k, vb + 2 ≤ k → k < vb + 2 + NENC → F k) {σ : Locals}
    {d d' : VSt} {enc value : Nat} (hσ : σ "enc" = BitVec.ofNat 32 enc) (hv : σ "value" = BitVec.ofNat 32 value)
    (hs : vmcs_writez_spec enc value d = some d') : Step εR c i0 MS F (writezS vb) σ d (σ.set "_" 0) d' := by
  unfold vmcs_writez_spec at hs
  by_cases hc : flags d ∧ valid_enc enc = true
  · rw [if_pos hc] at hs; cases hs; exact vmwrite_step εR c i0 hvb hF hσ (enc_ok hc.2).1 hv
  · rw [if_neg hc] at hs; cases hs

/-- `lo = vmread(enc); hi = vmread(enc + 1);` -/
def readz64S (vb : Nat) : Stmt APrim :=
  .seq (vmreadS vb "lo" (.var "enc")) (vmreadS vb "hi" (.bin .add (.var "enc") (.const 1)))

theorem readz64_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) {σ : Locals} {d : VSt} {enc : Nat} {lo hi : Val}
    (hσ : σ "enc" = BitVec.ofNat 32 enc) (hs : vmcs_readz64_spec enc d = some (lo, hi)) :
    Step εR c i0 MS F (readz64S vb) σ d ((σ.set "lo" lo).set "hi" hi) d := by
  unfold vmcs_readz64_spec at hs
  by_cases hc : flags d ∧ valid_enc enc = true
  · rw [if_pos hc] at hs
    obtain ⟨k1, k2⟩ := enc_ok hc.2
    cases e1 : d.vmcs.data enc with
    | none => rw [e1] at hs; cases hs
    | some a =>
      cases e2 : d.vmcs.data (enc + 1) with
      | none => rw [e1, e2] at hs; cases hs
      | some b =>
        rw [e1, e2] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact (vmread_step εR c i0 hvb "lo" (by decide) (e := .var "enc") hσ k1 e1).seq
          (vmread_step εR c i0 hvb "hi" (by decide) (k := enc + 1)
            (by simp [Expr.eval, BinOp.eval, Locals.set, hσ, BitVec.ofNat_add]) k2 e2)
  · rw [if_neg hc] at hs; cases hs

/-- `vmwrite(enc, lo); vmwrite(enc + 1, hi);` -/
def writez64S (vb : Nat) : Stmt APrim :=
  .seq (vmwriteS vb (.var "enc") (.var "lo")) (vmwriteS vb (.bin .add (.var "enc") (.const 1)) (.var "hi"))

theorem writez64_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) (hF : ∀ k, vb + 2 ≤ k → k < vb + 2 + NENC → F k) {σ : Locals}
    {d d' : VSt} {enc : Nat} {lo hi : Val} (hσ : σ "enc" = BitVec.ofNat 32 enc) (hl : σ "lo" = lo) (hh : σ "hi" = hi)
    (hs : vmcs_writez64_spec enc lo hi d = some d') :
    Step εR c i0 MS F (writez64S vb) σ d ((σ.set "_" 0).set "_" 0) d' := by
  unfold vmcs_writez64_spec at hs
  by_cases hc : flags d ∧ valid_enc enc = true
  · rw [if_pos hc] at hs; cases hs
    obtain ⟨k1, k2⟩ := enc_ok hc.2
    exact (vmwrite_step εR c i0 hvb hF (e := .var "enc") (v := .var "lo") hσ k1 hl).seq
      (vmwrite_step εR c i0 hvb hF (k := enc + 1) (by simp [Expr.eval, BinOp.eval, Locals.set, hσ, BitVec.ofNat_add])
        k2 (by simp [Expr.eval, Locals.set, hh]))
  · rw [if_neg hc] at hs; cases hs

/-- `c = vmcs_read32(VMCS_PRI_PROC_BASED_CTLS); if (enable == 1) c |= 4; else c &= ~4;
vmcs_write32(VMCS_PRI_PROC_BASED_CTLS, c);` -/
def setIntwinS (vb : Nat) : Stmt APrim :=
  .seq (vmreadS vb "c" (.const (BitVec.ofNat 32 C_VMCS_PRI_PROC_BASED_CTLS)))
    (.seq (.ite (.bin .eq (.var "enable") (.const 1)) (.assign "c" (.bin .bor (.var "c") (.const 4)))
        (.assign "c" (.bin .band (.var "c") (.const NOT_INTWIN))))
      (vmwriteS vb (.const (BitVec.ofNat 32 C_VMCS_PRI_PROC_BASED_CTLS)) (.var "c")))

theorem setIntwin_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) (hF : ∀ k, vb + 2 ≤ k → k < vb + 2 + NENC → F k) {σ : Locals}
    {d d' : VSt} {enable : Nat} (hen : σ "enable" = BitVec.ofNat 32 enable) (he32 : enable < 2 ^ 32)
    (hs : vmx_set_intercept_intwin_spec enable d = some d') : ∃ σ', Step εR c i0 MS F (setIntwinS vb) σ d σ' d' := by
  unfold vmx_set_intercept_intwin_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    have hk : C_VMCS_PRI_PROC_BASED_CTLS < NENC := by unfold C_VMCS_PRI_PROC_BASED_CTLS NENC; omega
    cases ec : d.vmcs.data C_VMCS_PRI_PROC_BASED_CTLS with
    | none => rw [ec] at hs; cases hs
    | some cv =>
      rw [ec] at hs; simp only at hs
      have R := vmread_step (F := F) εR c i0 hvb "c" (by decide) (σ := σ)
        (e := .const (BitVec.ofNat 32 C_VMCS_PRI_PROC_BASED_CTLS)) rfl hk ec
      have hen' : (σ.set "c" cv) "enable" = BitVec.ofNat 32 enable := by simp [Locals.set, hen]
      by_cases t : enable = 1
      · rw [if_pos t] at hs; cases hs
        exact ⟨_, R.seq ((Step.ite_true (eqc_true (b := 1) hen' t) (Step.assign "c" (by decide) _)).seq
          (vmwrite_step εR c i0 hvb hF (e := .const (BitVec.ofNat 32 C_VMCS_PRI_PROC_BASED_CTLS)) (v := .var "c") rfl hk
            (by simp [Expr.eval, BinOp.eval, Locals.set])))⟩
      · rw [if_neg t] at hs; cases hs
        exact ⟨_, R.seq ((Step.ite_false (eqc_false (b := 1) hen' he32 (by decide) t) (Step.assign "c" (by decide) _)).seq
          (vmwrite_step εR c i0 hvb hF (e := .const (BitVec.ofNat 32 C_VMCS_PRI_PROC_BASED_CTLS)) (v := .var "c") rfl hk
            (by simp [Expr.eval, BinOp.eval, Locals.set])))⟩
  · rw [if_neg hc] at hs; cases hs

/-- The selection of a segment's four encodings from `seg_encode`. -/
def selS : List (Nat × (Nat × Nat × Nat × Nat)) → Stmt APrim
  | [] => .skip
  | (k, (b, l, a, s)) :: t =>
    .ite (.bin .eq (.var "seg") (.const (BitVec.ofNat 32 k)))
      (.seq (.assign "eb" (.const (BitVec.ofNat 32 b))) (.seq (.assign "el" (.const (BitVec.ofNat 32 l)))
        (.seq (.assign "ea" (.const (BitVec.ofNat 32 a))) (.assign "es" (.const (BitVec.ofNat 32 s))))))
      (selS t)

theorem sel_step : ∀ (t : List (Nat × (Nat × Nat × Nat × Nat))) (σ : Locals) (d : VSt) {seg b l a s : Nat},
    σ "seg" = BitVec.ofNat 32 seg → seg < 2 ^ 32 → (∀ k p, (k, p) ∈ t → k < 2 ^ 32) →
    lookup t seg = some (b, l, a, s) →
    ∃ σ', Step εR c i0 MS F (selS t) σ d σ' d ∧ σ' "eb" = BitVec.ofNat 32 b ∧ σ' "el" = BitVec.ofNat 32 l ∧
      σ' "ea" = BitVec.ofNat 32 a ∧ σ' "es" = BitVec.ofNat 32 s ∧
      ∀ z, z ≠ "eb" → z ≠ "el" → z ≠ "ea" → z ≠ "es" → σ' z = σ z
  | [], _, _, _, _, _, _, _, _, _, _, hl => by cases hl
  | (k, (b0, l0, a0, s0)) :: t, σ, d, seg, b, l, a, s, hs, hseg, hk, hl => by
    unfold lookup at hl
    have hk0 : k < 2 ^ 32 := hk k _ (List.mem_cons_self ..)
    by_cases e : seg = k
    · rw [if_pos e] at hl; simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
      refine ⟨_, Step.ite_true (eqc_true hs e) ((Step.assign "eb" (by decide) _).seq ((Step.assign "el" (by decide) _).seq
        ((Step.assign "ea" (by decide) _).seq (Step.assign "es" (by decide) _)))), by simp [Locals.set, Expr.eval],
        by simp [Locals.set, Expr.eval], by simp [Locals.set, Expr.eval], by simp [Locals.set, Expr.eval],
        fun z h1 h2 h3 h4 => by simp [Locals.set, h1, h2, h3, h4]⟩
    · rw [if_neg e] at hl
      obtain ⟨σ', S, r⟩ := sel_step t σ d hs hseg (fun k' p hm => hk k' p (List.mem_cons_of_mem _ hm)) hl
      exact ⟨σ', Step.ite_false (eqc_false hs hseg hk0 e) S, r⟩

/-- `vmcs_write32(seg_encode[seg].base, base); vmcs_write32(seg_encode[seg].limit, lim);
if (seg != GUEST_GDTR && seg != GUEST_IDTR) { vmcs_write32(.access, ar); vmcs_write32(.selector, sel); }` -/
def setDescS (vb : Nat) : Stmt APrim :=
  .seq (selS seg_table)
    (.seq (vmwriteS vb (.var "eb") (.var "base"))
      (.seq (vmwriteS vb (.var "el") (.var "lim"))
        (.ite (.bin .eq (.var "seg") (.const 8)) .skip
          (.ite (.bin .eq (.var "seg") (.const 9)) .skip
            (.seq (vmwriteS vb (.var "ea") (.var "ar")) (vmwriteS vb (.var "es") (.var "sel")))))))

theorem seg_entries {seg b l a s : Nat} (h : lookup seg_table seg = some (b, l, a, s)) :
    seg < 10 ∧ b < NENC ∧ l < NENC ∧ (seg < 8 → a < NENC ∧ s < NENC) := by
  unfold seg_table at h
  simp only [lookup] at h
  unfold NENC
  repeat' (split at h)
  all_goals (first | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega) | cases h)

theorem setDesc_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) (hF : ∀ k, vb + 2 ≤ k → k < vb + 2 + NENC → F k) {σ : Locals}
    {d d' : VSt} {seg : Nat} {sel base lim ar : Val} (hs0 : σ "seg" = BitVec.ofNat 32 seg) (hsel : σ "sel" = sel)
    (hb : σ "base" = base) (hl : σ "lim" = lim) (ha : σ "ar" = ar)
    (hs : vmx_set_desc_spec seg sel base lim ar d = some d') : ∃ σ', Step εR c i0 MS F (setDescS vb) σ d σ' d' := by
  unfold vmx_set_desc_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    cases hd : vmx_set_desc_aux seg sel base lim ar d.vmcs.data with
    | none => rw [hd] at hs; cases hs
    | some dt =>
      rw [hd] at hs; simp only [Option.some.injEq] at hs; subst hs
      unfold vmx_set_desc_aux at hd
      cases hlk : lookup seg_table seg with
      | none => rw [hlk] at hd; cases hd
      | some p =>
        obtain ⟨eb, el, ea, es⟩ := p
        rw [hlk] at hd; simp only at hd
        obtain ⟨h10, hbE, hlE, hras⟩ := seg_entries hlk
        obtain ⟨σ1, S1, e1, e2, e3, e4, fr⟩ := sel_step (F := F) εR c i0 seg_table σ d hs0 (by omega)
          (by intro k p hm; simp [seg_table] at hm; omega) hlk
        have g : ∀ z, z = "seg" ∨ z = "sel" ∨ z = "base" ∨ z = "lim" ∨ z = "ar" → σ1 z = σ z := by
          rintro z (rfl | rfl | rfl | rfl | rfl) <;> exact fr _ (by decide) (by decide) (by decide) (by decide)
        have W1 := vmwrite_step (F := F) εR c i0 hvb hF (σ := σ1) (d := d) (e := .var "eb") (v := .var "base")
          (k := eb) (w := base) e1 hbE (by simp [Expr.eval, g "base" (by simp), hb])
        have W2 := vmwrite_step (F := F) εR c i0 hvb hF (σ := σ1.set "_" 0)
          (d := setData d (setAt d.vmcs.data eb (some base))) (e := .var "el") (v := .var "lim") (k := el) (w := lim)
          (by simp [Expr.eval, Locals.set, e2]) hlE (by simp [Expr.eval, Locals.set, g "lim" (by simp), hl])
        have hseg1 : ((σ1.set "_" 0).set "_" 0) "seg" = BitVec.ofNat 32 seg := by
          simp [Locals.set, g "seg" (by simp), hs0]
        by_cases h8 : seg < 8
        · rw [if_pos h8] at hd; simp only [Option.some.injEq] at hd; subst hd
          obtain ⟨haE, hsE⟩ := hras h8
          have W3 := vmwrite_step (F := F) εR c i0 hvb hF (σ := (σ1.set "_" 0).set "_" 0)
            (d := setData (setData d (setAt d.vmcs.data eb (some base)))
              (setAt (setAt d.vmcs.data eb (some base)) el (some lim))) (e := .var "ea") (v := .var "ar")
            (k := ea) (w := ar) (by simp [Expr.eval, Locals.set, e3]) haE
            (by simp [Expr.eval, Locals.set, g "ar" (by simp), ha])
          have W4 := vmwrite_step (F := F) εR c i0 hvb hF (σ := ((σ1.set "_" 0).set "_" 0).set "_" 0)
            (d := setData (setData (setData d (setAt d.vmcs.data eb (some base)))
              (setAt (setAt d.vmcs.data eb (some base)) el (some lim)))
              (setAt (setAt (setAt d.vmcs.data eb (some base)) el (some lim)) ea (some ar)))
            (e := .var "es") (v := .var "sel") (k := es) (w := sel) (by simp [Expr.eval, Locals.set, e4]) hsE
            (by simp [Expr.eval, Locals.set, g "sel" (by simp), hsel])
          exact ⟨_, S1.seq (W1.seq (W2.seq (Step.ite_false (eqc_false (b := 8) hseg1 (by omega) (by decide) (by omega))
            (Step.ite_false (eqc_false (b := 9) hseg1 (by omega) (by decide) (by omega)) (W3.seq W4)))))⟩
        · rw [if_neg h8] at hd; simp only [Option.some.injEq] at hd; subst hd
          by_cases e8 : seg = 8
          · exact ⟨_, S1.seq (W1.seq (W2.seq (Step.ite_true (eqc_true (b := 8) hseg1 e8) Step.skip)))⟩
          · have e9 : seg = 9 := by omega
            exact ⟨_, S1.seq (W1.seq (W2.seq (Step.ite_false (eqc_false (b := 8) hseg1 (by omega) (by decide) e8)
              (Step.ite_true (eqc_true (b := 9) hseg1 e9) Step.skip))))⟩
  · rw [if_neg hc] at hs; cases hs

/-- \`i = vmread(ENTRY_INTR_INFO); if ((i & VALID) == 0) { i2 = VALID | type | vector;
if (ev == 1) { vmwrite(ENTRY_INTR_INFO, i2 | 2048); vmwrite(ENTRY_EXCEPTION_ERROR, errcode); }
else vmwrite(ENTRY_INTR_INFO, i2); }\` -/
def injectEventS (vb : Nat) : Stmt APrim :=
  .seq (vmreadS vb "i" (.const (BitVec.ofNat 32 C_VMCS_ENTRY_INTR_INFO)))
    (.ite (.bin .eq (.bin .band (.var "i") (.const VALID)) (.const 0))
      (.seq (.assign "i2" (.bin .bor (.bin .bor (.const VALID) (.var "type")) (.var "vector")))
        (.ite (.bin .eq (.var "ev") (.const 1))
          (.seq (vmwriteS vb (.const (BitVec.ofNat 32 C_VMCS_ENTRY_INTR_INFO)) (.bin .bor (.var "i2") (.const 2048)))
            (vmwriteS vb (.const (BitVec.ofNat 32 C_VMCS_ENTRY_EXCEPTION_ERROR)) (.var "errcode")))
          (vmwriteS vb (.const (BitVec.ofNat 32 C_VMCS_ENTRY_INTR_INFO)) (.var "i2"))))
      .skip)

theorem injectEvent_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) (hF : ∀ k, vb + 2 ≤ k → k < vb + 2 + NENC → F k)
    {σ : Locals} {d d' : VSt} {type vector errcode : Val} {ev : Nat} (ht : σ "type" = type)
    (hv : σ "vector" = vector) (herr : σ "errcode" = errcode) (hev : σ "ev" = BitVec.ofNat 32 ev)
    (hev32 : ev < 2 ^ 32) (hs : vmx_inject_event_spec type vector errcode ev d = some d') :
    ∃ σ', Step εR c i0 MS F (injectEventS vb) σ d σ' d' := by
  unfold vmx_inject_event_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    have hk : C_VMCS_ENTRY_INTR_INFO < NENC := by unfold C_VMCS_ENTRY_INTR_INFO NENC; omega
    have hk2 : C_VMCS_ENTRY_EXCEPTION_ERROR < NENC := by unfold C_VMCS_ENTRY_EXCEPTION_ERROR NENC; omega
    cases ei : d.vmcs.data C_VMCS_ENTRY_INTR_INFO with
    | none => rw [ei] at hs; cases hs
    | some iv =>
      rw [ei] at hs; simp only at hs
      have R := vmread_step (F := F) εR c i0 hvb "i" (by decide) (σ := σ)
        (e := .const (BitVec.ofNat 32 C_VMCS_ENTRY_INTR_INFO)) rfl hk ei
      by_cases hz : iv &&& VALID = 0
      · rw [if_pos hz] at hs
        have hc1 : ¬ (Expr.bin .eq (.bin .band (.var "i") (.const VALID)) (.const 0)).eval (σ.set "i" iv) = 0 := by
          simp [Expr.eval, BinOp.eval, Locals.set]; exact hz
        have A := Step.assign (εR := εR) (c := c) (i := i0) (M := MS) (F := F) (d := d) (σ := σ.set "i" iv) "i2"
          (by decide) (.bin .bor (.bin .bor (.const VALID) (.var "type")) (.var "vector"))
        have hi2 : ((σ.set "i" iv).set "i2" ((VALID ||| type) ||| vector)) "i2" = (VALID ||| type) ||| vector := by
          simp [Locals.set]
        have hA : (Expr.bin .bor (.bin .bor (.const VALID) (.var "type")) (.var "vector")).eval (σ.set "i" iv)
            = (VALID ||| type) ||| vector := by simp [Expr.eval, BinOp.eval, Locals.set, ht, hv]
        rw [hA] at A
        have hev' : ((σ.set "i" iv).set "i2" ((VALID ||| type) ||| vector)) "ev" = BitVec.ofNat 32 ev := by
          simp [Locals.set, hev]
        by_cases e1 : ev = 1
        · rw [if_pos e1] at hs; cases hs
          exact ⟨_, R.seq (Step.ite_true hc1 (A.seq (Step.ite_true (eqc_true (b := 1) hev' e1)
            ((vmwrite_step εR c i0 hvb hF (e := .const (BitVec.ofNat 32 C_VMCS_ENTRY_INTR_INFO))
              (v := .bin .bor (.var "i2") (.const 2048)) rfl hk (by simp [Expr.eval, BinOp.eval, hi2])).seq
             (vmwrite_step εR c i0 hvb hF (e := .const (BitVec.ofNat 32 C_VMCS_ENTRY_EXCEPTION_ERROR))
              (v := .var "errcode") rfl hk2 (by simp [Expr.eval, Locals.set, herr]))))))⟩
        · rw [if_neg e1] at hs; cases hs
          exact ⟨_, R.seq (Step.ite_true hc1 (A.seq (Step.ite_false (eqc_false (b := 1) hev' hev32 (by decide) e1)
            (vmwrite_step εR c i0 hvb hF (e := .const (BitVec.ofNat 32 C_VMCS_ENTRY_INTR_INFO))
              (v := .var "i2") rfl hk (by simp [Expr.eval, hi2])))))⟩
      · rw [if_neg hz] at hs; cases hs
        have hc0 : (Expr.bin .eq (.bin .band (.var "i") (.const VALID)) (.const 0)).eval (σ.set "i" iv) = 0 := by
          simp [Expr.eval, BinOp.eval, Locals.set]; exact hz
        exact ⟨_, R.seq (Step.ite_false hc0 Step.skip)⟩
  · rw [if_neg hc] at hs; cases hs

/-- \`c = vmread(enc); r = (c & mask) == 0 ? 0 : 1;\` -/
def testBitS (vb enc : Nat) (mask : Val) : Stmt APrim :=
  .seq (vmreadS vb "c" (.const (BitVec.ofNat 32 enc)))
    (.ite (.bin .eq (.bin .band (.var "c") (.const mask)) (.const 0)) (.assign "r" (.const 0)) (.assign "r" (.const 1)))

theorem testBit_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) {enc : Nat} {mask : Val} (hk : enc < NENC) {σ : Locals}
    {d : VSt} {r : Val} (hs : testBit enc mask d = some r) :
    ∃ σ', Step εR c i0 MS F (testBitS vb enc mask) σ d σ' d ∧ σ' "r" = r := by
  unfold testBit at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    cases ec : d.vmcs.data enc with
    | none => rw [ec] at hs; cases hs
    | some cv =>
      rw [ec] at hs; simp only at hs
      have R := vmread_step (F := F) εR c i0 hvb "c" (by decide) (σ := σ) (e := .const (BitVec.ofNat 32 enc)) rfl hk ec
      by_cases hz : cv &&& mask = 0
      · rw [if_pos hz] at hs; cases hs
        exact ⟨_, R.seq (Step.ite_true (by simp [Expr.eval, BinOp.eval, Locals.set, hz]) (Step.assign "r" (by decide) _)),
          by simp [Locals.set, Expr.eval]⟩
      · rw [if_neg hz] at hs; cases hs
        exact ⟨_, R.seq (Step.ite_false (by simp [Expr.eval, BinOp.eval, Locals.set]; exact hz) (Step.assign "r" (by decide) _)),
          by simp [Locals.set, Expr.eval]⟩
  · rw [if_neg hc] at hs; cases hs

theorem checkPending_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) {σ : Locals} {d : VSt} {r : Val}
    (hs : vmx_check_pending_event_spec d = some r) :
    ∃ σ', Step εR c i0 MS F (testBitS vb C_VMCS_ENTRY_INTR_INFO VALID) σ d σ' d ∧ σ' "r" = r :=
  testBit_step εR c i0 hvb (by unfold C_VMCS_ENTRY_INTR_INFO NENC; omega) hs

theorem checkIntShadow_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) {σ : Locals} {d : VSt} {r : Val}
    (hs : vmx_check_int_shadow_spec d = some r) :
    ∃ σ', Step εR c i0 MS F (testBitS vb C_VMCS_GUEST_INTERRUPTIBILITY 3) σ d σ' d ∧ σ' "r" = r :=
  testBit_step εR c i0 hvb (by unfold C_VMCS_GUEST_INTERRUPTIBILITY NENC; omega) hs

/-- \`x = vmread(EXIT_REASON); r = x & 0xffff;\` -/
def exitReasonS (vb : Nat) : Stmt APrim :=
  .seq (vmreadS vb "x" (.const (BitVec.ofNat 32 C_VMCS_EXIT_REASON))) (.assign "r" (.bin .band (.var "x") (.const 65535)))

theorem exitReason_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) {σ : Locals} {d : VSt} {r : Val}
    (hs : vmx_get_exit_reason_spec d = some r) :
    ∃ σ', Step εR c i0 MS F (exitReasonS vb) σ d σ' d ∧ σ' "r" = r := by
  unfold vmx_get_exit_reason_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    cases ex : d.vmcs.data C_VMCS_EXIT_REASON with
    | none => rw [ex] at hs; cases hs
    | some xv =>
      rw [ex] at hs; simp only [Option.some.injEq] at hs; subst hs
      exact ⟨_, (vmread_step (F := F) εR c i0 hvb "x" (by decide) (σ := σ)
        (e := .const (BitVec.ofNat 32 C_VMCS_EXIT_REASON)) rfl (by unfold C_VMCS_EXIT_REASON NENC; omega) ex).seq
        (Step.assign "r" (by decide) _), by simp [Locals.set, Expr.eval, BinOp.eval]⟩
  · rw [if_neg hc] at hs; cases hs

/-- \`r = vmread(GUEST_PHYSICAL_ADDRESS)\` -/
def exitFaultAddrS (vb : Nat) : Stmt APrim := vmreadS vb "r" (.const (BitVec.ofNat 32 C_VMCS_GUEST_PHYSICAL_ADDRESS))

theorem exitFaultAddr_step (hvb : vb + 2 + NENC ≤ 2 ^ 32) {σ : Locals} {d : VSt} {r : Val}
    (hs : vmx_get_exit_fault_addr_spec d = some r) : Step εR c i0 MS F (exitFaultAddrS vb) σ d (σ.set "r" r) d := by
  unfold vmx_get_exit_fault_addr_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    exact vmread_step εR c i0 hvb "r" (by decide) (e := .const (BitVec.ofNat 32 C_VMCS_GUEST_PHYSICAL_ADDRESS)) rfl
      (by unfold C_VMCS_GUEST_PHYSICAL_ADDRESS NENC; omega) hs
  · rw [if_neg hc] at hs; cases hs

end Code

end VVMCS
