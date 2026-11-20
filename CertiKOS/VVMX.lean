import CertiKOS.VVMCS

/-!
# Virtualization: the VMX layer, ported from the Coq version

Transcribed from `coq/VMX.v`, which ports mCertiKOS's `objects/ObjVMX.v`.

The state combines three parts, in disjoint blocks of the kernel region:
* the `vmx` structure at `xb`: guest registers, exit information, saved host
  registers (36 words);
* the VMCS at `vb` (`VVMCS`);
* the EPT at `eb` (`VEPT`).

* `MatchX`: the three blocks hold what the abstract state knows.
* `xload_step`, `xstore_step`, `vread_step`, `vwrite_step`, `liftE`: the
  accesses to each block, as steps of the combined state.
* `readz_step`, `writez_step`, `getReg_step`, `setReg_step`,
  `nextEip_step`, `ioWidth_step`, `ioWrite_step`, `ioRep_step`,
  `ioStr_step`, `ioPort_step`, `setMmap_step`: **each function refines its
  specification.**
* `vmRun_step`: **entering the guest.** `vm_run` (`vmx_enter_pre`, then
  `vmx_enter`) saves the host `ebp` and `edi`, copies the guest `eip` into
  the VMCS and loads the guest registers into the processor's registers (the
  locals `EAX`, `EBX`, `EDX`, `ESI`, `EDI`, `EBP`, `RA`).
* `return_step`: **leaving the guest.** `vmx_return_from_guest` (`vmx_exit`,
  then `vmx_exit_post`) saves the guest registers, restores the host `edi`
  and `ebp`, and copies `eip`, the exit reason and the exit qualification out
  of the VMCS.

The code is what runs between the hardware transitions. The transitions
themselves (`vmlaunch` and the VM exit) belong to the machine and change only
the flag `ihost`.

What differs from `coq/VMX.v`:
* Fields and registers are machine words (`Val`).
* A step fixes the locals it ends with, so the registers loaded by `vm_run`
  and the host registers loaded by `vmx_return_from_guest` must be known
  (`some`) in the abstract state. The Coq theorems say: where they are known,
  the processor's registers hold them.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace VVMX

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MPTIntro
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)
open VVMCS (NENC MatchV vmreadS vmwriteS encE eval_enc)
open VEPT (NPG MatchE)

/-! ## Abstract data -/

structure XSt where
  ikern : Bool
  pg : Bool
  ihost : Bool
  init : Bool
  /-- the `vmx` structure, 36 words -/
  vmx : Nat → Option Val
  vmcs : VVMCS.VMCS
  ept : VEPT.EPT

/-- The view of the EPT layer. -/
def toE (d : XSt) : VEPT.VData := ⟨d.ikern, d.pg, d.ihost, d.ept⟩

def setVmx (d : XSt) (x : Nat → Option Val) : XSt := { d with vmx := x }
def setData (d : XSt) (dt : Nat → Option Val) : XSt := { d with vmcs := { d.vmcs with data := dt } }
def setEpt (d : XSt) (e : VEPT.EPT) : XSt := { d with ept := e }
def setIhost (d : XSt) (b : Bool) : XSt := { d with ihost := b }

def VMX_G_RAX' : Nat := 0
def VMX_G_RBX' : Nat := 2
def VMX_G_RDX' : Nat := 6
def VMX_G_RSI' : Nat := 8
def VMX_G_RDI' : Nat := 10
def VMX_G_RBP' : Nat := 12
def VMX_G_RIP' : Nat := 14
def VMX_G_CR2' : Nat := 16
def VMX_EXIT_REASON' : Nat := 27
def VMX_EXIT_QUALIFICATION' : Nat := 28
def VMX_LAUNCHED' : Nat := 31
def VMX_HOST_EBP' : Nat := 33
def VMX_HOST_EDI' : Nat := 34
def VMX_Size' : Nat := 36

def C_VMCS_GUEST_RIP : Nat := 26654
def C_VMCS_GUEST_RSP : Nat := 26652
def C_VMCS_GUEST_RFLAGS : Nat := 26656
def C_VMCS_GUEST_CR0 : Nat := 26624
def C_VMCS_GUEST_CR3 : Nat := 26626
def C_VMCS_GUEST_CR4 : Nat := 26628
def C_VMCS_EXIT_INSTRUCTION_LENGTH : Nat := 17420
def C_VMCS_EXIT_QUALIFICATION : Nat := 25600
def C_VMCS_EXIT_REASON : Nat := 17410

/-- Where each guest register lives: a word of `vmx`, or a VMCS field. -/
inductive RegT
  | vmcs (z : Nat)
  | vmx (z : Nat)

def reg_table : List (Nat × RegT) :=
  [(0, .vmx 0), (1, .vmx 2), (2, .vmx 4), (3, .vmx 6), (4, .vmx 8), (5, .vmx 10), (11, .vmx 16), (6, .vmx 12),
   (8, .vmx 14), (7, .vmcs 26652), (9, .vmcs 26656), (10, .vmcs 26624), (12, .vmcs 26626), (13, .vmcs 26628)]

def lookup : List (Nat × RegT) → Nat → Option RegT
  | [], _ => none
  | (k, r) :: t, x => if x = k then some r else lookup t x

/-! ## Specifications (`ObjVMX.v`) -/

section Specs
variable (maxpage : Nat)

def flags (d : XSt) : Prop := d.ikern = true ∧ d.pg = true ∧ d.ihost = true

instance (d : XSt) : Decidable (flags d) := by unfold flags; exact inferInstance

def vmx_readz_spec (i : Nat) (d : XSt) : Option Val :=
  if flags d ∧ i < VMX_Size' then d.vmx i else none

def vmx_writez_spec (i value : Nat) (d : XSt) : Option XSt :=
  if flags d ∧ i < VMX_Size' then some (setVmx d (setAt d.vmx i (some (BitVec.ofNat 32 value)))) else none

def vmx_get_reg_spec (reg : Nat) (d : XSt) : Option Val :=
  if flags d then
    match lookup reg_table reg with
    | some (.vmx z) => d.vmx z
    | some (.vmcs z) => d.vmcs.data z
    | none => none
  else none

def vmx_set_reg_spec (reg v : Nat) (d : XSt) : Option XSt :=
  if flags d then
    match lookup reg_table reg with
    | some (.vmx z) => some (setVmx d (setAt d.vmx z (some (BitVec.ofNat 32 v))))
    | some (.vmcs z) => some (setData d (setAt d.vmcs.data z (some (BitVec.ofNat 32 v))))
    | none => none
  else none

def vmx_get_next_eip_spec (d : XSt) : Option Val :=
  if flags d then
    match d.vmx VMX_G_RIP', d.vmcs.data C_VMCS_EXIT_INSTRUCTION_LENGTH with
    | some v1, some v2 => some (v1 + v2)
    | _, _ => none
  else none

def qual (d : XSt) : Option Val := if flags d then d.vmx VMX_EXIT_QUALIFICATION' else none

def vmx_get_io_width_spec (d : XSt) : Option Val :=
  match qual d with
  | some q => if q &&& 7 = 0 then some 0 else if q &&& 7 = 1 then some 1 else some 2
  | none => none

def vmx_get_io_write_spec (d : XSt) : Option Val :=
  match qual d with
  | some q => if (q / 8) &&& 1 = 1 then some 0 else some 1
  | none => none

def vmx_get_exit_io_rep_spec (d : XSt) : Option Val :=
  match qual d with
  | some q => some ((q / 32) &&& 1)
  | none => none

def vmx_get_exit_io_str_spec (d : XSt) : Option Val :=
  match qual d with
  | some q => some ((q / 16) &&& 1)
  | none => none

def vmx_get_exit_io_port_spec (d : XSt) : Option Val :=
  match qual d with
  | some q => some (q / 65536)
  | none => none

/-- `vmx_set_mmap`: add the mapping, then invalidate the EPT TLB. -/
def vmx_set_mmap_spec (gpa hpa memtype : Nat) (d : XSt) : Option (XSt × Nat) :=
  match VEPT.ept_add_mapping_spec maxpage gpa hpa memtype (toE d) with
  | some (e', res) =>
    if res < 2 ^ 32 ∧ memtype < 4096 then
      if res = 0 then
        match VEPT.ept_invalidate_mappings_spec e' with
        | some z => some (setEpt d e'.ept, z)
        | none => none
      else some (setEpt d e'.ept, res)
    else none
  | none => none

/-- `vm_run_spec`: the guest's `eip` goes to the VMCS, the host's `ebp` and
`edi` are saved, and the processor is in guest mode. -/
def vm_run_spec (rebp redi : Val) (d : XSt) : Option XSt :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true ∧ d.init = true then
    match d.vmx VMX_G_RIP' with
    | some v =>
      some (setIhost (setVmx (setData d (setAt d.vmcs.data C_VMCS_GUEST_RIP (some v)))
        (setAt (setAt d.vmx VMX_HOST_EBP' (some rebp)) VMX_HOST_EDI' (some redi))) false)
    | none => none
  else none

/-- `vmx_return_from_guest_spec`: the guest registers at the exit are saved,
`eip`, the exit reason and the exit qualification come out of the VMCS, and
the processor is in host mode. -/
def vmx_return_from_guest_spec (redi reax rebx redx resi rebp : Val) (d : XSt) : Option XSt :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = false ∧ d.init = true then
    let x6 := setAt (setAt (setAt (setAt (setAt (setAt d.vmx VMX_G_RDI' (some redi)) VMX_G_RAX' (some reax))
      VMX_G_RBX' (some rebx)) VMX_G_RDX' (some redx)) VMX_G_RSI' (some resi)) VMX_G_RBP' (some rebp)
    match d.vmcs.data C_VMCS_GUEST_RIP, d.vmcs.data C_VMCS_EXIT_REASON, d.vmcs.data C_VMCS_EXIT_QUALIFICATION with
    | some v1, some v2, some v3 =>
      some (setIhost (setVmx d (setAt (setAt (setAt (setAt x6 VMX_G_RIP' (some v1)) VMX_EXIT_REASON' (some v2))
        VMX_EXIT_QUALIFICATION' (some v3)) VMX_LAUNCHED' (some 1))) true)
    | _, _, _ => none
  else none

end Specs

/-! ## The three blocks in the region -/

def MatchX (xb vb eb : Nat) (d : XSt) (b : Region) : Prop :=
  (∀ i v, i < VMX_Size' → d.vmx i = some v → b (xb + i) = v) ∧ MatchV vb d.vmcs b ∧ MatchE eb (toE d) b

/-- The footprint: the three blocks. -/
def XF (xb vb eb : Nat) (k : Nat) : Prop :=
  (xb ≤ k ∧ k < xb + VMX_Size') ∨ (vb + 2 ≤ k ∧ k < vb + 2 + NENC) ∨ (eb ≤ k ∧ k < eb + NPG)

def FE (eb : Nat) (k : Nat) : Prop := eb ≤ k ∧ k < eb + NPG

theorem matchV_frame {vb : Nat} {v : VVMCS.VMCS} {b b' : Region} (h : MatchV vb v b)
    (hf : ∀ a, vb ≤ a → a < vb + 2 + NENC → b' a = b a) : MatchV vb v b' :=
  ⟨fun r hr => (hf _ (by omega) (by omega)).trans (h.1 r hr),
   fun a ha => (hf _ (by omega) (by omega)).trans (h.2.1 a ha),
   fun e x he hx => (hf _ (by omega) (by omega)).trans (h.2.2 e x he hx)⟩

theorem matchE_frame {eb : Nat} {e : VEPT.VData} {b b' : Region} (h : MatchE eb e b)
    (hf : ∀ a, eb ≤ a → a < eb + NPG → b' a = b a) : MatchE eb e b' :=
  fun g v hg hl => (hf _ (by omega) (by omega)).trans (h g v hg hl)

/-- `&vmx.field`: the cell `xb + i`. -/
def xaddr (xb i : Nat) : Expr := .const (BitVec.ofNat 32 (xb + i))
def xloadS (xb : Nat) (x : Ident) (i : Nat) : Stmt APrim := .call x .pull [lkE, xaddr xb i]
def xstoreS (xb i : Nat) (e : Expr) : Stmt APrim := .call "_" .push [lkE, xaddr xb i, e]

/-- The step ends somewhere else that the region matches as well. -/
theorem Step.post {εR : REnv} {c : CPU} {i0 : Nat} {D : Type} {M : D → Region → Prop} {F : Nat → Prop}
    {s : Stmt APrim} {σ σ' : Locals} {d d1 d2 : D} (h : Step εR c i0 M F s σ d σ' d1)
    (hM : ∀ b, M d1 b → M d2 b) : Step εR c i0 M F s σ d σ' d2 := by
  refine ⟨h.1, fun l b hlk hcs hm => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l b hlk hcs hm
  exact ⟨l1, b1, r1, c1, hM b1 m1, f1⟩

theorem eqz_true {e : Expr} {σ : Locals} {a b : Val} (ha : e.eval σ = a) (h : a = b) :
    ¬ (Expr.bin .eq e (.const b)).eval σ = 0 := by
  show ¬ BinOp.eval .eq (e.eval σ) b = 0
  rw [ha, h]; simp [BinOp.eval]

theorem eqz_false {e : Expr} {σ : Locals} {a b : Val} (ha : e.eval σ = a) (h : ¬ a = b) :
    (Expr.bin .eq e (.const b)).eval σ = 0 := by
  show BinOp.eval .eq (e.eval σ) b = 0
  rw [ha]; simp [BinOp.eval, h]

section Code
variable {xb vb eb maxpage : Nat}
variable (hxv : xb + 36 ≤ vb) (hve : vb + 65540 ≤ eb) (heb : eb + 1048576 ≤ 2 ^ 32) (hmp : maxpage ≤ NPG)
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MX" => MatchX xb vb eb
local notation "XFP" => XF xb vb eb

include hxv hve heb

theorem hvb' : vb + 2 + NENC ≤ 2 ^ 32 := by unfold NENC; omega
theorem heb' : eb + NPG ≤ 2 ^ 32 := by unfold NPG; omega

theorem match_vmx_write {d : XSt} {b : Region} {i : Nat} (w : Val) (hM : MX d b) (hi : i < VMX_Size') :
    MX (setVmx d (setAt d.vmx i (some w))) (setCell b (xb + i) w) := by
  unfold VMX_Size' at hi
  refine ⟨fun j v hj hv => ?_, matchV_frame hM.2.1 (fun a h1 h2 => sc_ne _ _ (by omega)),
    matchE_frame hM.2.2 (fun a h1 h2 => sc_ne _ _ (by omega))⟩
  have hv' : setAt d.vmx i (some w) j = some v := hv
  by_cases e : j = i
  · subst e; rw [setAt_eq] at hv'; cases hv'; exact sc_eq _ _ _
  · rw [setAt_ne _ _ e] at hv'; rw [sc_ne _ _ (by omega)]; exact hM.1 j v hj hv'

theorem match_vmcs_write {d : XSt} {b : Region} {k : Nat} (w : Val) (hM : MX d b) (hk : k < NENC) :
    MX (setData d (setAt d.vmcs.data k (some w))) (setCell b (vb + 2 + k) w) := by
  refine ⟨fun j v hj hv => ?_, VVMCS.match_write w hM.2.1 hk,
    matchE_frame hM.2.2 (fun a h1 h2 => sc_ne _ _ (by unfold NENC at hk; omega))⟩
  unfold VMX_Size' at hj
  rw [sc_ne _ _ (by omega)]; exact hM.1 j v (by unfold VMX_Size'; omega) hv

theorem eval_x {σ : Locals} {i : Nat} (hi : i < VMX_Size') : ((xaddr xb i).eval σ).toNat = xb + i := by
  unfold VMX_Size' at hi; exact tn (by omega)

theorem xload_step (x : Ident) (hx : x ≠ "lk") {σ : Locals} {d : XSt} {i : Nat} {v : Val} (hi : i < VMX_Size')
    (hv : d.vmx i = some v) : Step εR c i0 MX XFP (xloadS xb x i) σ d (σ.set x v) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (xaddr xb i) (eval_x hxv hve heb hi)
  rw [hM.1 i v hi hv] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem xstore_step {σ : Locals} {d : XSt} {i : Nat} {e : Expr} {w : Val} (hi : i < VMX_Size')
    (hw : e.eval σ = w) :
    Step εR c i0 MX XFP (xstoreS xb i e) σ d (σ.set "_" 0) (setVmx d (setAt d.vmx i (some w))) := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (xaddr xb i) e (eval_x hxv hve heb hi) hw
  exact ⟨l', _, hr, hcs', match_vmx_write hxv hve heb w hM hi,
    fun j hj => sc_ne _ _ (fun ee => hj (Or.inl ⟨by omega, by omega⟩))⟩

theorem vread_step (x : Ident) (hx : x ≠ "lk") {σ : Locals} {d : XSt} {e : Expr} {k : Nat} {w : Val}
    (he : e.eval σ = BitVec.ofNat 32 k) (hk : k < NENC) (hd : d.vmcs.data k = some w) :
    Step εR c i0 MX XFP (vmreadS vb x e) σ d (σ.set x w) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (encE vb e) (eval_enc (hvb' hxv hve heb) he hk)
  rw [hM.2.1.2.2 k w hk hd] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem vwrite_step {σ : Locals} {d : XSt} {e v : Expr} {k : Nat} {w : Val} (he : e.eval σ = BitVec.ofNat 32 k)
    (hk : k < NENC) (hv : v.eval σ = w) :
    Step εR c i0 MX XFP (vmwriteS vb e v) σ d (σ.set "_" 0) (setData d (setAt d.vmcs.data k (some w))) := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (encE vb e) v (eval_enc (hvb' hxv hve heb) he hk) hv
  exact ⟨l', _, hr, hcs', match_vmcs_write hxv hve heb w hM hk,
    fun j hj => sc_ne _ _ (fun ee => hj (Or.inr (Or.inl ⟨by omega, by omega⟩)))⟩

/-- A step of the EPT layer is a step of the combined state. -/
theorem liftE {s : Stmt APrim} {σ σ' : Locals} {d : XSt} {e1 : VEPT.VData}
    (h : Step εR c i0 (MatchE eb) (FE eb) s σ (toE d) σ' e1) : Step εR c i0 MX XFP s σ d σ' (setEpt d e1.ept) := by
  refine ⟨h.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l b hlk hcs hM.2.2
  refine ⟨l1, b1, r1, c1, ⟨fun i v hi hv => ?_, matchV_frame hM.2.1 (fun a h1 h2 => f1 a ?_), m1⟩,
    fun k hk => f1 k (fun h' => hk (Or.inr (Or.inr h')))⟩
  · unfold VMX_Size' at hi
    rw [f1 _ (by unfold FE; omega)]; exact hM.1 i v (by unfold VMX_Size'; omega) hv
  · unfold FE; unfold NENC at h2; omega

/-! ### `vmx_readz`, `vmx_writez` -/

def readzS (xb : Nat) : Stmt APrim := .call "r" .pull [lkE, .bin .add (.const (BitVec.ofNat 32 xb)) (.var "i")]
def writezS (xb : Nat) : Stmt APrim := .call "_" .push [lkE, .bin .add (.const (BitVec.ofNat 32 xb)) (.var "i"), .var "value"]

theorem eval_xi {σ : Locals} {i : Nat} (hσ : σ "i" = BitVec.ofNat 32 i) (hi : i < VMX_Size') :
    ((Expr.bin .add (.const (BitVec.ofNat 32 xb)) (.var "i")).eval σ).toNat = xb + i := by
  unfold VMX_Size' at hi
  show (BitVec.ofNat 32 xb + σ "i").toNat = _
  rw [hσ, BitVec.toNat_add, tn (by omega), tn (by omega)]; omega

theorem readz_step {σ : Locals} {d : XSt} {i : Nat} {r : Val} (hσ : σ "i" = BitVec.ofNat 32 i)
    (hs : vmx_readz_spec i d = some r) : Step εR c i0 MX XFP (readzS xb) σ d (σ.set "r" r) d := by
  unfold vmx_readz_spec at hs
  by_cases hc : flags d ∧ i < VMX_Size'
  · rw [if_pos hc] at hs
    refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
    have hr := rd_run (εR := εR) hcs hlk "r" _ (eval_xi hxv hve heb hσ hc.2)
    rw [hM.1 i r hc.2 hs] at hr
    exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem writez_step {σ : Locals} {d d' : XSt} {i value : Nat} (hσ : σ "i" = BitVec.ofNat 32 i)
    (hv : σ "value" = BitVec.ofNat 32 value) (hs : vmx_writez_spec i value d = some d') :
    Step εR c i0 MX XFP (writezS xb) σ d (σ.set "_" 0) d' := by
  unfold vmx_writez_spec at hs
  by_cases hc : flags d ∧ i < VMX_Size'
  · rw [if_pos hc] at hs; cases hs
    have hi := hc.2
    refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
    obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk _ (.var "value") (eval_xi hxv hve heb hσ hi) hv
    unfold VMX_Size' at hi
    exact ⟨l', _, hr, hcs', match_vmx_write hxv hve heb _ hM hc.2,
      fun j hj => sc_ne _ _ (fun ee => hj (Or.inl ⟨by omega, by unfold VMX_Size'; omega⟩))⟩
  · rw [if_neg hc] at hs; cases hs

/-! ### `vmx_get_reg`, `vmx_set_reg`: a `switch` on the register -/

def regGetBody (xb vb : Nat) : RegT → Stmt APrim
  | .vmx z => xloadS xb "r" z
  | .vmcs z => vmreadS vb "r" (.const (BitVec.ofNat 32 z))

def regSetBody (xb vb : Nat) : RegT → Stmt APrim
  | .vmx z => xstoreS xb z (.var "v")
  | .vmcs z => vmwriteS vb (.const (BitVec.ofNat 32 z)) (.var "v")

def switchS (body : RegT → Stmt APrim) : List (Nat × RegT) → Stmt APrim
  | [] => .skip
  | (k, r) :: t => .ite (.bin .eq (.var "reg") (.const (BitVec.ofNat 32 k))) (body r) (switchS body t)

def getRegS (xb vb : Nat) : Stmt APrim := switchS (regGetBody xb vb) reg_table
def setRegS (xb vb : Nat) : Stmt APrim := switchS (regSetBody xb vb) reg_table

omit hxv hve heb in
theorem switch_step (body : RegT → Stmt APrim) : ∀ (t : List (Nat × RegT)) (σ σ' : Locals) (d d' : XSt)
    (reg : Nat) (r : RegT), σ "reg" = BitVec.ofNat 32 reg → reg < 2 ^ 32 → (∀ x ∈ t, x.1 < 2 ^ 32) →
    lookup t reg = some r → Step εR c i0 MX XFP (body r) σ d σ' d' → Step εR c i0 MX XFP (switchS body t) σ d σ' d'
  | [], _, _, _, _, _, _, _, _, _, hl, _ => by cases hl
  | (k, r0) :: t, σ, σ', d, d', reg, r, hs, hreg, hk, hl, hb => by
    unfold lookup at hl
    by_cases e : reg = k
    · rw [if_pos e] at hl; cases hl; exact Step.ite_true (eqc_true hs e) hb
    · rw [if_neg e] at hl
      exact Step.ite_false (eqc_false hs hreg (hk (k, r0) (List.mem_cons_self ..)) e)
        (switch_step body t σ σ' d d' reg r hs hreg (fun x hm => hk x (List.mem_cons_of_mem _ hm)) hl hb)

omit hxv hve heb in
theorem reg_keys : ∀ x ∈ reg_table, x.1 < 2 ^ 32 := by decide

def RegT.okb : RegT → Bool
  | .vmx z => decide (z < VMX_Size')
  | .vmcs z => decide (z < NENC)

omit hxv hve heb in
theorem lookup_mem : ∀ (t : List (Nat × RegT)) (x : Nat) (r : RegT), lookup t x = some r → (x, r) ∈ t
  | [], _, _, h => by cases h
  | (k, r0) :: t, x, r, h => by
    unfold lookup at h
    by_cases e : x = k
    · rw [if_pos e] at h; cases h; subst e; exact List.mem_cons_self ..
    · rw [if_neg e] at h; exact List.mem_cons_of_mem _ (lookup_mem t x r h)

omit hxv hve heb in
theorem reg_bounds {reg : Nat} {t : RegT} (h : lookup reg_table reg = some t) : reg < 14 ∧ t.okb = true := by
  have hall : ∀ p ∈ reg_table, p.1 < 14 ∧ p.2.okb = true := by decide
  exact hall _ (lookup_mem _ _ _ h)

theorem getReg_step {σ : Locals} {d : XSt} {reg : Nat} {r : Val} (hσ : σ "reg" = BitVec.ofNat 32 reg)
    (hs : vmx_get_reg_spec reg d = some r) : Step εR c i0 MX XFP (getRegS xb vb) σ d (σ.set "r" r) d := by
  unfold vmx_get_reg_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    cases hl : lookup reg_table reg with
    | none => rw [hl] at hs; cases hs
    | some t =>
      rw [hl] at hs
      obtain ⟨h14, hb⟩ := reg_bounds hl
      refine switch_step εR c i0 _ reg_table σ _ d d reg t hσ (by omega) reg_keys hl ?_
      cases t with
      | vmx z => exact xload_step hxv hve heb εR c i0 "r" (by decide) (of_decide_eq_true hb) hs
      | vmcs z => exact vread_step hxv hve heb εR c i0 "r" (by decide) (e := .const (BitVec.ofNat 32 z)) rfl (of_decide_eq_true hb) hs
  · rw [if_neg hc] at hs; cases hs

theorem setReg_step {σ : Locals} {d d' : XSt} {reg v : Nat} (hσ : σ "reg" = BitVec.ofNat 32 reg)
    (hv : σ "v" = BitVec.ofNat 32 v) (hs : vmx_set_reg_spec reg v d = some d') :
    Step εR c i0 MX XFP (setRegS xb vb) σ d (σ.set "_" 0) d' := by
  unfold vmx_set_reg_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    cases hl : lookup reg_table reg with
    | none => rw [hl] at hs; cases hs
    | some t =>
      rw [hl] at hs
      obtain ⟨h14, hb⟩ := reg_bounds hl
      refine switch_step εR c i0 _ reg_table σ _ d d' reg t hσ (by omega) reg_keys hl ?_
      cases t with
      | vmx z =>
        simp only [Option.some.injEq] at hs; subst hs
        exact xstore_step hxv hve heb εR c i0 (of_decide_eq_true hb) (by simp [Expr.eval, hv])
      | vmcs z =>
        simp only [Option.some.injEq] at hs; subst hs
        exact vwrite_step hxv hve heb εR c i0 (e := .const (BitVec.ofNat 32 z)) rfl (of_decide_eq_true hb) (by simp [Expr.eval, hv])
  · rw [if_neg hc] at hs; cases hs

/-! ### `vmx_get_next_eip`: `r = vmx.g_rip + vmcs_read32(VMCS_EXIT_INSTRUCTION_LENGTH);` -/

def nextEipS (xb vb : Nat) : Stmt APrim :=
  .seq (xloadS xb "t" VMX_G_RIP')
    (.seq (vmreadS vb "u" (.const (BitVec.ofNat 32 C_VMCS_EXIT_INSTRUCTION_LENGTH)))
      (.assign "r" (.bin .add (.var "t") (.var "u"))))

theorem nextEip_step {σ : Locals} {d : XSt} {r : Val} (hs : vmx_get_next_eip_spec d = some r) :
    ∃ σ', Step εR c i0 MX XFP (nextEipS xb vb) σ d σ' d ∧ σ' "r" = r := by
  unfold vmx_get_next_eip_spec at hs
  by_cases hc : flags d
  · rw [if_pos hc] at hs
    cases e1 : d.vmx VMX_G_RIP' with
    | none => rw [e1] at hs; cases hs
    | some v1 =>
      cases e2 : d.vmcs.data C_VMCS_EXIT_INSTRUCTION_LENGTH with
      | none => rw [e1, e2] at hs; cases hs
      | some v2 =>
        rw [e1, e2] at hs; simp only [Option.some.injEq] at hs; subst hs
        exact ⟨_, (xload_step hxv hve heb εR c i0 "t" (by decide) (by decide) e1).seq
          ((vread_step hxv hve heb εR c i0 "u" (by decide) (e := .const (BitVec.ofNat 32 C_VMCS_EXIT_INSTRUCTION_LENGTH))
            rfl (by unfold C_VMCS_EXIT_INSTRUCTION_LENGTH NENC; omega) e2).seq (Step.assign "r" (by decide) _)),
          by simp [Locals.set, Expr.eval, BinOp.eval]⟩
  · rw [if_neg hc] at hs; cases hs

/-! ### The exit qualification -/

def loadQualS (xb : Nat) : Stmt APrim := xloadS xb "q" VMX_EXIT_QUALIFICATION'

theorem qual_step {σ : Locals} {d : XSt} {q : Val} (hq : qual d = some q) :
    Step εR c i0 MX XFP (loadQualS xb) σ d (σ.set "q" q) d := by
  unfold qual at hq
  by_cases hc : flags d
  · rw [if_pos hc] at hq; exact xload_step hxv hve heb εR c i0 "q" (by decide) (by decide) hq
  · rw [if_neg hc] at hq; cases hq

/-- `sz = q & 7; r = sz == 0 ? SZ8 : sz == 1 ? SZ16 : SZ32;` -/
def ioWidthS (xb : Nat) : Stmt APrim :=
  .seq (loadQualS xb)
    (.seq (.assign "sz" (.bin .band (.var "q") (.const 7)))
      (.ite (.bin .eq (.var "sz") (.const 0)) (.assign "r" (.const 0))
        (.ite (.bin .eq (.var "sz") (.const 1)) (.assign "r" (.const 1)) (.assign "r" (.const 2)))))

theorem ioWidth_step {σ : Locals} {d : XSt} {r : Val} (hs : vmx_get_io_width_spec d = some r) :
    ∃ σ', Step εR c i0 MX XFP (ioWidthS xb) σ d σ' d ∧ σ' "r" = r := by
  unfold vmx_get_io_width_spec at hs
  cases hq : qual d with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs; simp only at hs
    have Q := qual_step hxv hve heb εR c i0 (σ := σ) hq
    have A := (Step.assign (σ := σ.set "q" q) (d := d) (εR := εR) (c := c) (i := i0) (M := MX) (F := XFP) "sz" (by decide)
        (.bin .band (.var "q") (.const 7)))
    have hsz : (Expr.var "sz").eval ((σ.set "q" q).set "sz" ((Expr.bin .band (.var "q") (.const 7)).eval (σ.set "q" q)))
        = q &&& 7 := by simp [Expr.eval, BinOp.eval, Locals.set]
    by_cases t0 : q &&& 7 = 0
    · rw [if_pos t0] at hs; cases hs
      exact ⟨_, Q.seq (A.seq (Step.ite_true (eqz_true hsz t0) (Step.assign "r" (by decide) _))), by simp [Locals.set, Expr.eval]⟩
    · rw [if_neg t0] at hs
      by_cases t1 : q &&& 7 = 1
      · rw [if_pos t1] at hs; cases hs
        exact ⟨_, Q.seq (A.seq (Step.ite_false (eqz_false hsz t0) (Step.ite_true (eqz_true hsz t1)
          (Step.assign "r" (by decide) _)))), by simp [Locals.set, Expr.eval]⟩
      · rw [if_neg t1] at hs; cases hs
        exact ⟨_, Q.seq (A.seq (Step.ite_false (eqz_false hsz t0) (Step.ite_false (eqz_false hsz t1)
          (Step.assign "r" (by decide) _)))), by simp [Locals.set, Expr.eval]⟩

/-- `r = ((q >> 3) & 1) == EXIT_QUAL_IO_IN ? 0 : 1;` -/
def ioWriteS (xb : Nat) : Stmt APrim :=
  .seq (loadQualS xb)
    (.ite (.bin .eq (.bin .band (.bin .div (.var "q") (.const 8)) (.const 1)) (.const 1))
      (.assign "r" (.const 0)) (.assign "r" (.const 1)))

theorem ioWrite_step {σ : Locals} {d : XSt} {r : Val} (hs : vmx_get_io_write_spec d = some r) :
    ∃ σ', Step εR c i0 MX XFP (ioWriteS xb) σ d σ' d ∧ σ' "r" = r := by
  unfold vmx_get_io_write_spec at hs
  cases hq : qual d with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs; simp only at hs
    have Q := qual_step hxv hve heb εR c i0 (σ := σ) hq
    have he : (Expr.bin .band (.bin .div (.var "q") (.const 8)) (.const 1)).eval (σ.set "q" q) = (q / 8) &&& 1 := by
      simp [Expr.eval, BinOp.eval, Locals.set]
    by_cases t : (q / 8) &&& 1 = 1
    · rw [if_pos t] at hs; cases hs
      exact ⟨_, Q.seq (Step.ite_true (eqz_true he t) (Step.assign "r" (by decide) _)), by simp [Locals.set, Expr.eval]⟩
    · rw [if_neg t] at hs; cases hs
      exact ⟨_, Q.seq (Step.ite_false (eqz_false he t) (Step.assign "r" (by decide) _)), by simp [Locals.set, Expr.eval]⟩

/-- `r = (q >> k) & 1;` and `r = q >> 16;` -/
def qualFieldS (xb : Nat) (e : Expr) : Stmt APrim := .seq (loadQualS xb) (.assign "r" e)

def ioRepS (xb : Nat) : Stmt APrim := qualFieldS xb (.bin .band (.bin .div (.var "q") (.const 32)) (.const 1))
def ioStrS (xb : Nat) : Stmt APrim := qualFieldS xb (.bin .band (.bin .div (.var "q") (.const 16)) (.const 1))
def ioPortS (xb : Nat) : Stmt APrim := qualFieldS xb (.bin .div (.var "q") (.const 65536))

theorem qualField_step {σ : Locals} {d : XSt} {q : Val} (e : Expr) (hq : qual d = some q) :
    Step εR c i0 MX XFP (qualFieldS xb e) σ d ((σ.set "q" q).set "r" (e.eval (σ.set "q" q))) d :=
  (qual_step hxv hve heb εR c i0 hq).seq (Step.assign "r" (by decide) e)

theorem ioRep_step {σ : Locals} {d : XSt} {r : Val} (hs : vmx_get_exit_io_rep_spec d = some r) :
    ∃ σ', Step εR c i0 MX XFP (ioRepS xb) σ d σ' d ∧ σ' "r" = r := by
  unfold vmx_get_exit_io_rep_spec at hs
  cases hq : qual d with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
    exact ⟨_, qualField_step hxv hve heb εR c i0 _ hq, by simp [Locals.set, Expr.eval, BinOp.eval]⟩

theorem ioStr_step {σ : Locals} {d : XSt} {r : Val} (hs : vmx_get_exit_io_str_spec d = some r) :
    ∃ σ', Step εR c i0 MX XFP (ioStrS xb) σ d σ' d ∧ σ' "r" = r := by
  unfold vmx_get_exit_io_str_spec at hs
  cases hq : qual d with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
    exact ⟨_, qualField_step hxv hve heb εR c i0 _ hq, by simp [Locals.set, Expr.eval, BinOp.eval]⟩

theorem ioPort_step {σ : Locals} {d : XSt} {r : Val} (hs : vmx_get_exit_io_port_spec d = some r) :
    ∃ σ', Step εR c i0 MX XFP (ioPortS xb) σ d σ' d ∧ σ' "r" = r := by
  unfold vmx_get_exit_io_port_spec at hs
  cases hq : qual d with
  | none => rw [hq] at hs; cases hs
  | some q =>
    rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
    exact ⟨_, qualField_step hxv hve heb εR c i0 _ hq, by simp [Locals.set, Expr.eval, BinOp.eval]⟩

/-! ### `vmx_set_mmap`: `r = ept_add_mapping(gpa, hpa, mem_type); if (r == 0) r = ept_invalidate_mappings();` -/

def setMmapS (eb : Nat) : Stmt APrim :=
  .seq (VEPT.addMappingS eb) (.ite (.bin .eq (.var "r") (.const 0)) VEPT.invalidateS .skip)

include hmp in
theorem setMmap_step {σ : Locals} {d d' : XSt} {gpa hpa memtype r : Nat} (hg : σ "gpa" = BitVec.ofNat 32 gpa)
    (hh : σ "hpa" = BitVec.ofNat 32 hpa) (hm : σ "memtype" = BitVec.ofNat 32 memtype)
    (hs : vmx_set_mmap_spec maxpage gpa hpa memtype d = some (d', r)) :
    ∃ σ', Step εR c i0 MX XFP (setMmapS eb) σ d σ' d' ∧ σ' "r" = BitVec.ofNat 32 r := by
  unfold vmx_set_mmap_spec at hs
  cases ha : VEPT.ept_add_mapping_spec maxpage gpa hpa memtype (toE d) with
  | none => rw [ha] at hs; cases hs
  | some p =>
    obtain ⟨e', res⟩ := p
    rw [ha] at hs; simp only at hs
    obtain ⟨A, hr0⟩ := VEPT.addMapping_step (eb := eb) (maxpage := maxpage) (F := FE eb) εR c i0
      (heb' hxv hve heb) hmp (fun k h1 h2 => ⟨h1, h2⟩) hg hh hm ha
    subst hr0
    have L := liftE hxv hve heb εR c i0 A
    by_cases hc : memtype < 4096
    · have hc' : (0 < 2 ^ 32 ∧ memtype < 4096) := ⟨by decide, hc⟩
      rw [if_pos hc', if_pos rfl] at hs
      cases hi : VEPT.ept_invalidate_mappings_spec e' with
      | none => rw [hi] at hs; cases hs
      | some z =>
        rw [hi] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨-, hz⟩ := VEPT.invalidate_step (eb := eb) (F := FE eb) εR c i0 (σ := σ) hi
        subst hz
        exact ⟨_, L.seq (Step.ite_true (by simp [Expr.eval, BinOp.eval, Locals.set])
          (Step.assign "r" (by decide) (.const 0))), by simp [Locals.set, Expr.eval]⟩
    · have hc' : ¬ (0 < 2 ^ 32 ∧ memtype < 4096) := fun h => hc h.2
      rw [if_neg hc'] at hs; cases hs

/-! ### `vm_run`: `vmx_enter_pre` and `vmx_enter` -/

/-- `vmcs_write32(VMCS_GUEST_RIP, vmx.g_rip);` -/
def enterPreS (xb vb : Nat) : Stmt APrim :=
  .seq (xloadS xb "t" VMX_G_RIP') (vmwriteS vb (.const (BitVec.ofNat 32 C_VMCS_GUEST_RIP)) (.var "t"))

/-- `vmx_enter`: save the host `ebp` and `edi`, load the guest registers. -/
def enterS (xb : Nat) : Stmt APrim :=
  .seq (xstoreS xb VMX_HOST_EBP' (.var "EBP")) (.seq (xstoreS xb VMX_HOST_EDI' (.var "EDI"))
  (.seq (xloadS xb "EAX" VMX_G_RAX') (.seq (xloadS xb "EBX" VMX_G_RBX') (.seq (xloadS xb "EDX" VMX_G_RDX')
  (.seq (xloadS xb "ESI" VMX_G_RSI') (.seq (xloadS xb "EDI" VMX_G_RDI') (.seq (xloadS xb "EBP" VMX_G_RBP')
    (xloadS xb "RA" VMX_G_RIP'))))))))

def vmRunS (xb vb : Nat) : Stmt APrim := .seq (enterPreS xb vb) (enterS xb)

/-- **`vm_run` refines `vm_run_spec`.** The host `ebp` and `edi` are in `EBP`
and `EDI`; afterwards the guest registers are in the processor's registers. -/
theorem vmRun_step {σ : Locals} {d d' : XSt} {rebp redi a bx dx si di bp ip : Val} (hb : σ "EBP" = rebp)
    (hdi : σ "EDI" = redi) (ha : d.vmx VMX_G_RAX' = some a) (hbx : d.vmx VMX_G_RBX' = some bx)
    (hdx : d.vmx VMX_G_RDX' = some dx) (hsi : d.vmx VMX_G_RSI' = some si) (hdi' : d.vmx VMX_G_RDI' = some di)
    (hbp : d.vmx VMX_G_RBP' = some bp) (hip : d.vmx VMX_G_RIP' = some ip) (hs : vm_run_spec rebp redi d = some d') :
    ∃ σ', Step εR c i0 MX XFP (vmRunS xb vb) σ d σ' d' ∧ σ' "EAX" = a ∧ σ' "EBX" = bx ∧ σ' "EDX" = dx ∧
      σ' "ESI" = si ∧ σ' "EDI" = di ∧ σ' "EBP" = bp ∧ σ' "RA" = ip := by
  unfold vm_run_spec at hs
  by_cases hc : d.ikern = true ∧ d.pg = true ∧ d.ihost = true ∧ d.init = true
  · rw [if_pos hc, hip] at hs; simp only [Option.some.injEq] at hs; subst hs
    let d1 := setData d (setAt d.vmcs.data C_VMCS_GUEST_RIP (some ip))
    let d3 := setVmx d1 (setAt (setAt d.vmx VMX_HOST_EBP' (some rebp)) VMX_HOST_EDI' (some redi))
    have hx : ∀ i v, i ≠ VMX_HOST_EBP' → i ≠ VMX_HOST_EDI' → d.vmx i = some v → d3.vmx i = some v :=
      fun i v h1 h2 h => by
        show setAt (setAt d.vmx VMX_HOST_EBP' (some rebp)) VMX_HOST_EDI' (some redi) i = some v
        rw [setAt_ne _ _ h2, setAt_ne _ _ h1]; exact h
    have S1 := xload_step hxv hve heb εR c i0 "t" (by decide) (σ := σ) (by decide) hip
    have S2 := vwrite_step hxv hve heb εR c i0 (σ := σ.set "t" ip) (d := d)
      (e := .const (BitVec.ofNat 32 C_VMCS_GUEST_RIP)) (v := .var "t") (w := ip) rfl
      (by unfold C_VMCS_GUEST_RIP NENC; omega) (by simp [Expr.eval, Locals.set])
    have S3 := xstore_step hxv hve heb εR c i0 (σ := (σ.set "t" ip).set "_" 0) (d := d1) (i := VMX_HOST_EBP')
      (e := .var "EBP") (w := rebp) (by decide) (by simp [Expr.eval, Locals.set, hb])
    have S4 := xstore_step hxv hve heb εR c i0 (σ := ((σ.set "t" ip).set "_" 0).set "_" 0)
      (d := setVmx d1 (setAt d.vmx VMX_HOST_EBP' (some rebp))) (i := VMX_HOST_EDI')
      (e := .var "EDI") (w := redi) (by decide) (by simp [Expr.eval, Locals.set, hdi])
    have L := fun (x : Ident) (hx' : x ≠ "lk") (σ0 : Locals) (i : Nat) (v : Val) (hi : i < VMX_Size')
        (h1 : i ≠ VMX_HOST_EBP') (h2 : i ≠ VMX_HOST_EDI') (h : d.vmx i = some v) =>
      xload_step hxv hve heb εR c i0 x hx' (σ := σ0) (d := d3) hi (hx i v h1 h2 h)
    refine ⟨_, Step.post ((S1.seq S2).seq (S3.seq (S4.seq
      ((L "EAX" (by decide) _ _ _ (by decide) (by decide) (by decide) ha).seq
      ((L "EBX" (by decide) _ _ _ (by decide) (by decide) (by decide) hbx).seq
      ((L "EDX" (by decide) _ _ _ (by decide) (by decide) (by decide) hdx).seq
      ((L "ESI" (by decide) _ _ _ (by decide) (by decide) (by decide) hsi).seq
      ((L "EDI" (by decide) _ _ _ (by decide) (by decide) (by decide) hdi').seq
      ((L "EBP" (by decide) _ _ _ (by decide) (by decide) (by decide) hbp).seq
       (L "RA" (by decide) _ _ _ (by decide) (by decide) (by decide) hip))))))))))
      (fun b h => ⟨h.1, h.2.1, h.2.2⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Locals.set]
  · rw [if_neg hc] at hs; cases hs

/-! ### `vmx_return_from_guest`: `vmx_exit` and `vmx_exit_post` -/

/-- `vmx_exit`: save the guest registers, load the host `edi` and `ebp`. -/
def exitS (xb : Nat) : Stmt APrim :=
  .seq (xstoreS xb VMX_G_RDI' (.var "EDI")) (.seq (xstoreS xb VMX_G_RAX' (.var "EAX"))
  (.seq (xstoreS xb VMX_G_RBX' (.var "EBX")) (.seq (xstoreS xb VMX_G_RDX' (.var "EDX"))
  (.seq (xstoreS xb VMX_G_RSI' (.var "ESI")) (.seq (xstoreS xb VMX_G_RBP' (.var "EBP"))
  (.seq (xloadS xb "EDI" VMX_HOST_EDI') (xloadS xb "EBP" VMX_HOST_EBP')))))))

/-- `vmx.g_rip = vmcs_read32(VMCS_GUEST_RIP); vmx.exit_reason = vmcs_read32(VMCS_EXIT_REASON);
vmx.exit_qualification = vmcs_read32(VMCS_EXIT_QUALIFICATION); vmx.launched = 1;` -/
def exitPostS (xb vb : Nat) : Stmt APrim :=
  .seq (vmreadS vb "t" (.const (BitVec.ofNat 32 C_VMCS_GUEST_RIP))) (.seq (xstoreS xb VMX_G_RIP' (.var "t"))
  (.seq (vmreadS vb "t" (.const (BitVec.ofNat 32 C_VMCS_EXIT_REASON))) (.seq (xstoreS xb VMX_EXIT_REASON' (.var "t"))
  (.seq (vmreadS vb "t" (.const (BitVec.ofNat 32 C_VMCS_EXIT_QUALIFICATION)))
  (.seq (xstoreS xb VMX_EXIT_QUALIFICATION' (.var "t")) (xstoreS xb VMX_LAUNCHED' (.const 1)))))))

def returnS (xb vb : Nat) : Stmt APrim := .seq (exitS xb) (exitPostS xb vb)

/-- **`vmx_return_from_guest` refines `vmx_return_from_guest_spec`.** The guest
registers at the exit are in the processor's registers; afterwards the host
`edi` and `ebp` are back. -/
theorem return_step {σ : Locals} {d d' : XSt} {redi reax rebx redx resi rebp he hb : Val}
    (E1 : σ "EDI" = redi) (E2 : σ "EAX" = reax) (E3 : σ "EBX" = rebx) (E4 : σ "EDX" = redx) (E5 : σ "ESI" = resi)
    (E6 : σ "EBP" = rebp) (hhe : d.vmx VMX_HOST_EDI' = some he) (hhb : d.vmx VMX_HOST_EBP' = some hb)
    (hs : vmx_return_from_guest_spec redi reax rebx redx resi rebp d = some d') :
    ∃ σ', Step εR c i0 MX XFP (returnS xb vb) σ d σ' d' ∧ σ' "EDI" = he ∧ σ' "EBP" = hb := by
  unfold vmx_return_from_guest_spec at hs
  by_cases hc : d.ikern = true ∧ d.pg = true ∧ d.ihost = false ∧ d.init = true
  · rw [if_pos hc] at hs
    cases V1 : d.vmcs.data C_VMCS_GUEST_RIP with
    | none => rw [V1] at hs; cases hs
    | some v1 =>
    cases V2 : d.vmcs.data C_VMCS_EXIT_REASON with
    | none => rw [V1, V2] at hs; cases hs
    | some v2 =>
    cases V3 : d.vmcs.data C_VMCS_EXIT_QUALIFICATION with
    | none => rw [V1, V2, V3] at hs; cases hs
    | some v3 =>
    rw [V1, V2, V3] at hs; simp only [Option.some.injEq] at hs; subst hs
    let x6 := setAt (setAt (setAt (setAt (setAt (setAt d.vmx VMX_G_RDI' (some redi)) VMX_G_RAX' (some reax))
      VMX_G_RBX' (some rebx)) VMX_G_RDX' (some redx)) VMX_G_RSI' (some resi)) VMX_G_RBP' (some rebp)
    have h6 : ∀ i v, i ≠ 10 → i ≠ 0 → i ≠ 2 → i ≠ 6 → i ≠ 8 → i ≠ 12 → d.vmx i = some v → x6 i = some v := by
      intro i v n1 n2 n3 n4 n5 n6 h
      show setAt (setAt (setAt (setAt (setAt (setAt d.vmx 10 _) 0 _) 2 _) 6 _) 8 _) 12 _ i = _
      rw [setAt_ne _ _ n6, setAt_ne _ _ n5, setAt_ne _ _ n4, setAt_ne _ _ n3, setAt_ne _ _ n2, setAt_ne _ _ n1]
      exact h
    have X := fun (σ0 : Locals) (d0 : XSt) (i : Nat) (e : Expr) (w : Val) (hi : i < VMX_Size') (hw : e.eval σ0 = w) =>
      xstore_step hxv hve heb εR c i0 (σ := σ0) (d := d0) (i := i) (e := e) (w := w) hi hw
    have R := fun (σ0 : Locals) (d0 : XSt) (k : Nat) (w : Val) (hk : k < NENC) (hd : d0.vmcs.data k = some w) =>
      vread_step hxv hve heb εR c i0 "t" (by decide) (σ := σ0) (d := d0) (e := .const (BitVec.ofNat 32 k)) rfl hk hd
    refine ⟨_, Step.post (
      (( X _ _ VMX_G_RDI' (.var "EDI") redi (by decide) (by simp [Expr.eval, Locals.set, E1])).seq
      (( X _ _ VMX_G_RAX' (.var "EAX") reax (by decide) (by simp [Expr.eval, Locals.set, E2])).seq
      (( X _ _ VMX_G_RBX' (.var "EBX") rebx (by decide) (by simp [Expr.eval, Locals.set, E3])).seq
      (( X _ _ VMX_G_RDX' (.var "EDX") redx (by decide) (by simp [Expr.eval, Locals.set, E4])).seq
      (( X _ _ VMX_G_RSI' (.var "ESI") resi (by decide) (by simp [Expr.eval, Locals.set, E5])).seq
      (( X _ _ VMX_G_RBP' (.var "EBP") rebp (by decide) (by simp [Expr.eval, Locals.set, E6])).seq
      ((xload_step hxv hve heb εR c i0 "EDI" (by decide) (d := setVmx d x6) (by decide)
          (h6 _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hhe)).seq
       (xload_step hxv hve heb εR c i0 "EBP" (by decide) (d := setVmx d x6) (by decide)
          (h6 _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hhb))))))))).seq
      ((R _ (setVmx d x6) C_VMCS_GUEST_RIP v1 (by unfold C_VMCS_GUEST_RIP NENC; omega) (by exact V1)).seq
      ((X _ _ VMX_G_RIP' (.var "t") v1 (by decide) (by simp [Expr.eval, Locals.set])).seq
      ((R _ _ C_VMCS_EXIT_REASON v2 (by unfold C_VMCS_EXIT_REASON NENC; omega) (by exact V2)).seq
      ((X _ _ VMX_EXIT_REASON' (.var "t") v2 (by decide) (by simp [Expr.eval, Locals.set])).seq
      ((R _ _ C_VMCS_EXIT_QUALIFICATION v3 (by unfold C_VMCS_EXIT_QUALIFICATION NENC; omega) (by exact V3)).seq
      ((X _ _ VMX_EXIT_QUALIFICATION' (.var "t") v3 (by decide) (by simp [Expr.eval, Locals.set])).seq
       (X _ _ VMX_LAUNCHED' (.const 1) 1 (by decide) rfl)))))))) (fun b h => ⟨h.1, h.2.1, h.2.2⟩), ?_, ?_⟩ <;> simp [Locals.set]
  · rw [if_neg hc] at hs; cases hs

end Code

end VVMX
