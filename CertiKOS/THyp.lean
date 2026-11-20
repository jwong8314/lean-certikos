import CertiKOS.TTop

/-!
# The hypercalls, ported from the Coq version

Transcribed from `coq/Trap.v`, which ports the virtual machine's handlers of
mCertiKOS's trap layer (`objects/ObjTrap.v`, inside a comment there; the C is
in `trap/sys_*.c`).

Here a handler runs on the top state (`TTop.HData`): it reads its arguments
from the caller's user context (`uctx_arg2` …), calls the VMX layer, and
writes its results and error code back (`uctx_set_retval1` …,
`uctx_set_errno`). The Coq version keeps arguments and results in locals; the
accesses to the user context are the process layers', verified there.

* `body` specifications (`get_reg_x` …): the part of mCertiKOS's
  specification after the arguments are read, on the VMX state, with the list
  of registers it writes back (as in `coq/Trap.v`).
* `hcall`: the whole specification: run the body, then write the registers in
  order (`setRegs`), as mCertiKOS's `uctx_set_retval1_spec` then
  `uctx_set_errno_spec` do.
* `liftV`: a step of the VMCS layer is a step of the VMX state.
* `argH`, `setsH`, `xH`: reading an argument, writing results, and a step of
  the VMX layer, as steps of the top state.
* `getReg_triple` … : **each handler refines its specification.**

What differs from mCertiKOS: as in `coq/Trap.v`, `rdmsr` and `wrmsr` answer 0
(their model, `rdmsr_spec`, `wrmsr_spec`); the 64-bit TSC offset is its two
words.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace TTop

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MPTIntro PUCtxt TTrap
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)
open VVMX (XSt MatchX XF)

/-! ## Specifications (`coq/Trap.v`, `ObjTrap.v`) -/

def toV (x : XSt) : VVMCS.VSt := ⟨x.ikern, x.pg, x.ihost, x.vmcs⟩

/-- A VMCS writer on the VMX state, then `uctx_set_errno(E_SUCC)`. -/
def onV (r : Option VVMCS.VSt) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  match r with
  | some v => some ({ x with vmcs := v.vmcs }, [(U_EAX, 0)])
  | none => none

def E_INVAL_REG : Nat := 6
def E_INVAL_SEG : Nat := 7
def C_VMCS_TSC_OFFSET : Nat := 8208

/-- `sys_hvm_get_reg` after the argument. -/
def get_reg_x (reg : Nat) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  if reg < 14 then
    match VVMX.vmx_get_reg_spec reg x with
    | some v => some (x, [(U_EBX, v.toNat), (U_EAX, 0)])
    | none => none
  else some (x, [(U_EAX, E_INVAL_REG)])

def set_reg_x (reg v : Nat) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  if reg < 14 then
    match VVMX.vmx_set_reg_spec reg v x with
    | some x' => some (x', [(U_EAX, 0)])
    | none => none
  else some (x, [(U_EAX, E_INVAL_REG)])

def set_seg_x (seg sel base lim ar : Nat) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  if seg < 10 then
    onV (VVMCS.vmx_set_desc_spec seg (BitVec.ofNat 32 sel) (BitVec.ofNat 32 base) (BitVec.ofNat 32 lim)
      (BitVec.ofNat 32 ar) (toV x)) x
  else some (x, [(U_EAX, E_INVAL_SEG)])

def get_next_eip_x (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  match VVMX.vmx_get_next_eip_spec x with
  | some v => some (x, [(U_EBX, v.toNat), (U_EAX, 0)])
  | none => none

def inject_event_x (type vector errcode ev : Nat) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  onV (VVMCS.vmx_inject_event_spec (BitVec.ofNat 32 type) (BitVec.ofNat 32 vector) (BitVec.ofNat 32 errcode) ev
    (toV x)) x

def reader_x (r : Option Val) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  match r with
  | some v => some (x, [(U_EBX, v.toNat), (U_EAX, 0)])
  | none => none

def check_pending_x (x : XSt) := reader_x (VVMCS.vmx_check_pending_event_spec (toV x)) x
def check_int_shadow_x (x : XSt) := reader_x (VVMCS.vmx_check_int_shadow_spec (toV x)) x

def intercept_int_window_x (enable : Nat) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  onV (VVMCS.vmx_set_intercept_intwin_spec enable (toV x)) x

/-- `vmx_get_tsc_offset`: `vmcs_read64(VMCS_TSC_OFFSET)`; the high word is
return value 1, the low word return value 2. -/
def get_tsc_x (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  match VVMCS.vmcs_readz64_spec C_VMCS_TSC_OFFSET (toV x) with
  | some (lo, hi) => some (x, [(U_EBX, hi.toNat), (U_ECX, lo.toNat), (U_EAX, 0)])
  | none => none

/-- `vmx_set_tsc_offset((uint64_t) hi << 32 | lo)`: `vmcs_write64(VMCS_TSC_OFFSET, …)`. -/
def set_tsc_x (hi lo : Nat) (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  onV (VVMCS.vmcs_writez64_spec C_VMCS_TSC_OFFSET (BitVec.ofNat 32 lo) (BitVec.ofNat 32 hi) (toV x)) x

/-- Write the registers in order. -/
def setRegs : List (Nat × Nat) → UData → Option UData
  | [], u => some u
  | (r, n) :: t, u =>
    match uctx_set_reg_spec r n u with
    | some u' => setRegs t u'
    | none => none

/-- **A hypercall**: its body on the VMX state, then the registers it writes. -/
def hcall (r : Option (XSt × List (Nat × Nat))) (d : HData) : Option HData :=
  match r with
  | some (x, o) =>
    match setRegs o (putX d x).toUData with
    | some u => some { putX d x with toUData := u }
    | none => none
  | none => none

def trap_get_reg_spec (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData with
  | some reg => hcall (get_reg_x reg (toX d)) d
  | none => none

def trap_set_reg_spec (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData, uctx_arg3_spec d.toUData with
  | some reg, some v => hcall (set_reg_x reg v (toX d)) d
  | _, _ => none

def trap_get_next_eip_spec (d : HData) : Option HData := hcall (get_next_eip_x (toX d)) d
def trap_check_pending_event_spec (d : HData) : Option HData := hcall (check_pending_x (toX d)) d
def trap_check_int_shadow_spec (d : HData) : Option HData := hcall (check_int_shadow_x (toX d)) d
def trap_get_tsc_offset_spec (d : HData) : Option HData := hcall (get_tsc_x (toX d)) d

def trap_intercept_int_window_spec (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData with
  | some en => hcall (intercept_int_window_x en (toX d)) d
  | none => none

def trap_set_tsc_offset_spec (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData, uctx_arg3_spec d.toUData with
  | some hi, some lo => hcall (set_tsc_x hi lo (toX d)) d
  | _, _ => none

def trap_inject_event_spec (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData, uctx_arg3_spec d.toUData, uctx_arg4_spec d.toUData, uctx_arg5_spec d.toUData with
  | some t, some v, some e, some ev => hcall (inject_event_x t v e ev (toX d)) d
  | _, _, _, _ => none

def trap_set_seg_spec (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData, uctx_arg3_spec d.toUData, uctx_arg4_spec d.toUData, uctx_arg5_spec d.toUData,
    uctx_arg6_spec d.toUData with
  | some seg, some sel, some base, some lim, some ar => hcall (set_seg_x seg sel base lim ar (toX d)) d
  | _, _, _, _, _ => none

/-! ## The code -/

/-- Write registers from expressions, in order. -/
def setsS (cidb ucb : Nat) : List (Nat × Expr) → Stmt APrim
  | [] => .skip
  | (r, e) :: t => .seq (uctxSetRegS cidb ucb r e) (setsS cidb ucb t)

def errS (cidb ucb n : Nat) : Stmt APrim := setsS cidb ucb [(U_EAX, .const (BitVec.ofNat 32 n))]
def ret1S (cidb ucb : Nat) : Stmt APrim := setsS cidb ucb [(U_EBX, .var "r"), (U_EAX, .const 0)]

/-- `sys_hvm_get_reg`. -/
def getRegH (cidb ucb xb vb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "reg" U_EBX)
    (.ite (.bin .ltu (.var "reg") (.const 14)) (.seq (VVMX.getRegS xb vb) (ret1S cidb ucb)) (errS cidb ucb 6))

/-- `sys_hvm_set_reg`. -/
def setRegH (cidb ucb xb vb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "reg" U_EBX) (.seq (uctxArgS cidb ucb "v" U_ECX)
    (.ite (.bin .ltu (.var "reg") (.const 14)) (.seq (VVMX.setRegS xb vb) (errS cidb ucb 0)) (errS cidb ucb 6)))

/-- `sys_hvm_get_next_eip`. -/
def getNextEipH (cidb ucb xb vb : Nat) : Stmt APrim := .seq (VVMX.nextEipS xb vb) (ret1S cidb ucb)

def checkPendingH (cidb ucb vb : Nat) : Stmt APrim :=
  .seq (VVMCS.testBitS vb VVMCS.C_VMCS_ENTRY_INTR_INFO VVMCS.VALID) (ret1S cidb ucb)
def checkIntShadowH (cidb ucb vb : Nat) : Stmt APrim :=
  .seq (VVMCS.testBitS vb VVMCS.C_VMCS_GUEST_INTERRUPTIBILITY 3) (ret1S cidb ucb)

/-- `sys_hvm_intercept_int_window`. -/
def interceptH (cidb ucb vb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "enable" U_EBX) (.seq (VVMCS.setIntwinS vb) (errS cidb ucb 0))

/-- `sys_hvm_get_tsc_offset`. -/
def getTscH (cidb ucb vb : Nat) : Stmt APrim :=
  .seq (.assign "enc" (.const (BitVec.ofNat 32 C_VMCS_TSC_OFFSET))) (.seq (VVMCS.readz64S vb)
    (setsS cidb ucb [(U_EBX, .var "hi"), (U_ECX, .var "lo"), (U_EAX, .const 0)]))

/-- `sys_hvm_set_tsc_offset`. -/
def setTscH (cidb ucb vb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "hi" U_EBX) (.seq (uctxArgS cidb ucb "lo" U_ECX)
    (.seq (.assign "enc" (.const (BitVec.ofNat 32 C_VMCS_TSC_OFFSET))) (.seq (VVMCS.writez64S vb) (errS cidb ucb 0))))

/-- `sys_hvm_inject_event`. -/
def injectH (cidb ucb vb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "type" U_EBX) (.seq (uctxArgS cidb ucb "vector" U_ECX)
    (.seq (uctxArgS cidb ucb "errcode" U_EDX) (.seq (uctxArgS cidb ucb "ev" U_ESI)
      (.seq (VVMCS.injectEventS vb) (errS cidb ucb 0)))))

/-- `sys_hvm_set_seg`. -/
def setSegH (cidb ucb vb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "seg" U_EBX) (.seq (uctxArgS cidb ucb "sel" U_ECX)
    (.seq (uctxArgS cidb ucb "base" U_EDX) (.seq (uctxArgS cidb ucb "lim" U_ESI)
      (.seq (uctxArgS cidb ucb "ar" U_EDI)
        (.ite (.bin .ltu (.var "seg") (.const 10)) (.seq (VVMCS.setDescS vb) (errS cidb ucb 0)) (errS cidb ucb 7))))))

/-! ## Steps of the top state -/

section Steps
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- The footprint of a hypercall: the caller's registers and the VMX blocks. -/
def HF (ucb num_proc xb vb eb : Nat) (k : Nat) : Prop := UCF ucb num_proc k ∨ XF xb vb eb k

theorem heb_of (hL : HL) : eb + 1048576 ≤ 2 ^ 32 := by have := pb_lt hL; have := hL.hep; omega

/-- **A step of the VMCS layer is a step of the VMX state.** -/
theorem liftV (hL : HL) {s : Stmt APrim} {σ σ' : Locals} {x : XSt} {v : VVMCS.VSt}
    (h : Step εR c i0 (VVMCS.MatchS vb) (fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) s σ (toV x) σ' v) :
    Step εR c i0 (MatchX xb vb eb) (XF xb vb eb) s σ x σ' { x with vmcs := v.vmcs } := by
  have := hL.hxv; have := hL.hve
  refine ⟨h.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l b hlk hcs hM.2.1
  refine ⟨l1, b1, r1, c1, ⟨fun i w hi hw => ?_, m1, VVMX.matchE_frame hM.2.2 (fun a h1 h2 => f1 a ?_)⟩,
    fun k hk => f1 k (fun h' => hk (Or.inr (Or.inl h')))⟩
  · unfold VVMX.VMX_Size' at hi
    rw [f1 _ (by omega)]; exact hM.1 i w (by unfold VVMX.VMX_Size'; omega) hw
  · unfold VVMCS.NENC; omega

theorem hvb_of (hL : HL) : vb + 2 + VVMCS.NENC ≤ 2 ^ 32 := by
  have := heb_of hL; have := hL.hve; unfold VVMCS.NENC; omega

/-- A step of the VMCS layer, as a step of the top state. -/
theorem vH (hL : HL) {s : Stmt APrim} {σ σ' : Locals} {d : HData} {v : VVMCS.VSt}
    (h : Step εR c i0 (VVMCS.MatchS vb) (fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) s σ (toV (toX d)) σ' v) :
    Step εR c i0 MH (HF ucb num_proc xb vb eb) s σ d σ' (putX d { toX d with vmcs := v.vmcs }) :=
  (stepXH εR c i0 hL (liftV εR c i0 hL h)).widen (fun _ h => Or.inr h)

/-- A step of the VMX layer, as a step of the top state. -/
theorem xH (hL : HL) {s : Stmt APrim} {σ σ' : Locals} {d : HData} {x : XSt}
    (h : Step εR c i0 (MatchX xb vb eb) (XF xb vb eb) s σ (toX d) σ' x) :
    Step εR c i0 MH (HF ucb num_proc xb vb eb) s σ d σ' (putX d x) :=
  (stepXH εR c i0 hL h).widen (fun _ h => Or.inr h)

/-- Reading an argument. -/
theorem argH (hL : HL) (x : Ident) (hx : x ≠ "lk") {reg : Nat} (hreg : reg < 17) {σ : Locals} {d : HData} {a : Nat}
    (hcp : d.cid < num_proc) (ha : uctx_arg_spec reg d.toUData = some a) :
    Step εR c i0 MH (HF ucb num_proc xb vb eb) (uctxArgS cidb ucb x reg) σ d
      ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set x (BitVec.ofNat 32 a)) d :=
  (stepUH εR c i0 hL (F := fun _ => False)
    (uctxArgU (ida := ida) (cidb := cidb) εR c i0 hL.ulay x hx hreg (σ := σ) hcp (arg_val ha).1)
    (fun _ h => h.elim)).widen (fun _ h => h.elim)

theorem set_reg_cid {reg n : Nat} {u u' : UData} (h : uctx_set_reg_spec reg n u = some u') : u'.cid = u.cid := by
  obtain ⟨U, e⟩ := set_reg_shape h; rw [e]

/-- **Writing the results.** Each expression has its value whatever the
writes before it did to `curid` and `_`. -/
theorem setsH (hL : HL) : ∀ (l : List (Nat × Expr × Nat)) (σ : Locals) (d : HData) (u : UData),
    d.cid < num_proc →
    (∀ p ∈ l, p.1 < 17 ∧ ∀ τ : Locals, (∀ z, z ≠ "curid" → z ≠ "_" → τ z = σ z) →
      p.2.1.eval τ = BitVec.ofNat 32 p.2.2) →
    setRegs (l.map fun p => (p.1, p.2.2)) d.toUData = some u →
    ∃ σ', Step εR c i0 MH (HF ucb num_proc xb vb eb) (setsS cidb ucb (l.map fun p => (p.1, p.2.1))) σ d σ'
      { d with toUData := u } ∧ σ' "lk" = σ "lk"
  | [], σ, d, u, hcp, _, hs => by
    simp only [List.map, setRegs, Option.some.injEq] at hs
    subst hs
    exact ⟨σ, Step.skip, rfl⟩
  | (r, e, n) :: t, σ, d, u, hcp, hp, hs => by
    simp only [List.map, setRegs] at hs
    cases h1 : uctx_set_reg_spec r n d.toUData with
    | none => rw [h1] at hs; cases hs
    | some u1 =>
      rw [h1] at hs
      obtain ⟨hr, he⟩ := hp (r, e, n) (List.mem_cons_self ..)
      have S1 := (stepUH εR c i0 hL (d := d) (F := UCF ucb num_proc)
        (setReg_step (ida := ida) (cidb := cidb) εR c i0 hL.ulay (F := UCF ucb num_proc) (fun _ h => h) hr
          (ve := e) (σ := σ) (n := n) (he _ (fun z h1 h2 => by simp [Locals.set, h1])) hcp h1)
        (fun k hk => by have := hL.hob; unfold UCF at hk; omega)).widen
          (F' := HF ucb num_proc xb vb eb) (fun _ h => Or.inl h)
      have hcp1 : ({ d with toUData := u1 } : HData).cid < num_proc := by
        show u1.cid < num_proc; rw [set_reg_cid h1]; exact hcp
      obtain ⟨σ', S2, hl⟩ := setsH hL t ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "_" 0) { d with toUData := u1 } u
        hcp1 (fun p hm => ⟨(hp p (List.mem_cons_of_mem _ hm)).1, fun τ hτ =>
          (hp p (List.mem_cons_of_mem _ hm)).2 τ (fun z h1 h2 => by rw [hτ z h1 h2]; simp [Locals.set, h1, h2])⟩) hs
      exact ⟨σ', S1.seq S2, by rw [hl]; simp [Locals.set]⟩

/-- The tail `uctx_set_retval1(r); uctx_set_errno(E_SUCC);`. -/
theorem ret1H (hL : HL) {σ : Locals} {d : HData} {u : UData} {v : Val} (hcp : d.cid < num_proc)
    (hv : σ "r" = v) (hs : setRegs [(U_EBX, v.toNat), (U_EAX, 0)] d.toUData = some u) :
    ∃ σ', Step εR c i0 MH (HF ucb num_proc xb vb eb) (ret1S cidb ucb) σ d σ' { d with toUData := u } := by
  obtain ⟨σ', S, -⟩ := setsH (ida := ida) εR c i0 hL [(U_EBX, .var "r", v.toNat), (U_EAX, .const 0, 0)] σ d u hcp
    (by
      intro p hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨by dsimp only; decide, fun τ hτ => by
          show τ "r" = _; rw [hτ "r" (by decide) (by decide), hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
      · exact ⟨by dsimp only; decide, fun τ hτ => rfl⟩) hs
  exact ⟨σ', S⟩

/-- The tail `uctx_set_errno(n);`. -/
theorem errH (hL : HL) {σ : Locals} {d : HData} {u : UData} {n : Nat} (hcp : d.cid < num_proc)
    (hs : setRegs [(U_EAX, n)] d.toUData = some u) :
    ∃ σ', Step εR c i0 MH (HF ucb num_proc xb vb eb) (errS cidb ucb n) σ d σ' { d with toUData := u } := by
  obtain ⟨σ', S, -⟩ := setsH (ida := ida) εR c i0 hL [(U_EAX, .const (BitVec.ofNat 32 n), n)] σ d u hcp
    (by
      intro p hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm; exact ⟨by dsimp only; decide, fun τ hτ => rfl⟩) hs
  exact ⟨σ', S⟩

/-- `hcall` with its body known. -/
theorem hcall_some {r : Option (XSt × List (Nat × Nat))} {d d' : HData} (h : hcall r d = some d') :
    ∃ x o u, r = some (x, o) ∧ setRegs o (putX d x).toUData = some u ∧ d' = { putX d x with toUData := u } := by
  unfold hcall at h
  cases hr : r with
  | none => rw [hr] at h; cases h
  | some p =>
    obtain ⟨x, o⟩ := p
    rw [hr] at h; simp only at h
    cases hs : setRegs o (putX d x).toUData with
    | none => rw [hs] at h; cases h
    | some u => rw [hs] at h; simp only [Option.some.injEq] at h; exact ⟨x, o, u, rfl, hs, h.symm⟩

theorem guard_lt {σ : Locals} {x : Ident} {a b : Nat} (hx : σ x = BitVec.ofNat 32 a) (ha : a < 2 ^ 32)
    (hb : b < 2 ^ 32) : (Expr.bin .ltu (.var x) (.const (BitVec.ofNat 32 b))).eval σ = if a < b then 1 else 0 :=
  ltu_eval hx rfl ha hb

/-! ## The handlers -/

/-- **`sys_hvm_get_reg` refines `trap_get_reg_spec`.** -/
theorem getReg_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb) (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_get_reg_spec d = some d1)
      (getRegH cidb ucb xb vb) (fun _ d _ d' => trap_get_reg_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_get_reg_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some reg =>
    rw [e2] at hs; simp only at hs
    obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
    have hr32 := (arg_val e2).2
    have A := argH (ida := ida) εR c i0 hL "reg" (by decide) (reg := U_EBX) (by decide) (σ := σ) hcp e2
    let σ1 := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "reg" (BitVec.ofNat 32 reg)
    have hg := guard_lt (σ := σ1) (x := "reg") (a := reg) (b := 14) (by simp [σ1]) hr32 (by decide)
    unfold get_reg_x at hb
    by_cases t : reg < 14
    · rw [if_pos t] at hb hg
      cases hv : VVMX.vmx_get_reg_spec reg (toX d) with
      | none => rw [hv] at hb; cases hb
      | some v =>
        rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have B := xH (ida := ida) εR c i0 hL (VVMX.getReg_step hL.hxv hL.hve (heb_of hL) εR c i0 (σ := σ1) (by simp [σ1]) hv)
        obtain ⟨σ3, R⟩ := ret1H (ida := ida) εR c i0 hL (σ := σ1.set "r" v) (d := putX d (toX d)) hcp (by simp) hR
        exact ⟨_, _, A.seq (Step.ite_true (fun h => absurd (hg.symm.trans h) (by decide)) (B.seq R)), hs0⟩
    · rw [if_neg t] at hb hg
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨σ3, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ1) (d := putX d (toX d)) hcp hR
      exact ⟨_, _, A.seq (Step.ite_false (by exact hg) R), hs0⟩

/-- **`sys_hvm_set_reg` refines `trap_set_reg_spec`.** -/
theorem setReg_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb) (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_set_reg_spec d = some d1)
      (setRegH cidb ucb xb vb) (fun _ d _ d' => trap_set_reg_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_set_reg_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some reg =>
    cases e3 : uctx_arg3_spec d.toUData with
    | none => rw [e2, e3] at hs; cases hs
    | some v =>
      rw [e2, e3] at hs; simp only at hs
      obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
      have hr32 := (arg_val e2).2
      have A1 := argH (ida := ida) εR c i0 hL "reg" (by decide) (reg := U_EBX) (by decide) (σ := σ) hcp e2
      have A2 := argH (ida := ida) εR c i0 hL "v" (by decide) (reg := U_ECX) (by decide)
        (σ := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "reg" (BitVec.ofNat 32 reg)) hcp e3
      let σ2 := ((((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "reg" (BitVec.ofNat 32 reg)).set "curid"
        (BitVec.ofNat 32 d.cid)).set "v" (BitVec.ofNat 32 v))
      have hg := guard_lt (σ := σ2) (x := "reg") (a := reg) (b := 14) (by simp [σ2, Locals.set]) hr32 (by decide)
      unfold set_reg_x at hb
      by_cases t : reg < 14
      · rw [if_pos t] at hb hg
        cases hv : VVMX.vmx_set_reg_spec reg v (toX d) with
        | none => rw [hv] at hb; cases hb
        | some x1 =>
          rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have B := xH (ida := ida) εR c i0 hL (VVMX.setReg_step hL.hxv hL.hve (heb_of hL) εR c i0 (σ := σ2)
            (by simp [σ2, Locals.set]) (by simp [σ2]) hv)
          obtain ⟨σ3, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ2.set "_" 0) (d := putX d x1) hcp hR
          exact ⟨_, _, A1.seq (A2.seq (Step.ite_true (fun h => absurd (hg.symm.trans h) (by decide)) (B.seq R))), hs0⟩
      · rw [if_neg t] at hb hg
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨σ3, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ2) (d := putX d (toX d)) hcp hR
        exact ⟨_, _, A1.seq (A2.seq (Step.ite_false (by exact hg) R)), hs0⟩

/-- **`sys_hvm_get_next_eip` refines `trap_get_next_eip_spec`.** -/
theorem getNextEip_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_get_next_eip_spec d = some d1)
      (getNextEipH cidb ucb xb vb) (fun _ d _ d' => trap_get_next_eip_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_get_next_eip_spec at hs
  obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
  unfold get_next_eip_x at hb
  cases hv : VVMX.vmx_get_next_eip_spec (toX d) with
  | none => rw [hv] at hb; cases hb
  | some v =>
    rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨σ1, B, hr, -⟩ := VVMX.nextEip_step hL.hxv hL.hve (heb_of hL) εR c i0 (σ := σ) hv
    obtain ⟨σ3, R⟩ := ret1H (ida := ida) εR c i0 hL (σ := σ1) (d := putX d (toX d)) hcp hr hR
    exact ⟨_, _, (xH (ida := ida) εR c i0 hL B).seq R, hs0⟩

/-- A VMCS reader followed by `uctx_set_retval1(r); uctx_set_errno(E_SUCC);`. -/
theorem reader_triple (hL : HL) {s : Stmt APrim} {f : VVMCS.VSt → Option Val}
    (hstep : ∀ σ (v : VVMCS.VSt) r, f v = some r →
      ∃ σ', Step εR c i0 (VVMCS.MatchS vb) (fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) s σ v σ' v ∧ σ' "r" = r) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, hcall (reader_x (f (toV (toX d))) (toX d)) d = some d1)
      (.seq s (ret1S cidb ucb)) (fun _ d _ d' => hcall (reader_x (f (toV (toX d))) (toX d)) d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
  unfold reader_x at hb
  cases hv : f (toV (toX d)) with
  | none => rw [hv] at hb; cases hb
  | some v =>
    rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨σ1, B, hr⟩ := hstep σ _ v hv
    obtain ⟨σ3, R⟩ := ret1H (ida := ida) εR c i0 hL (σ := σ1) (d := putX d (toX d)) hcp hr hR
    exact ⟨_, _, (vH (ida := ida) εR c i0 hL B).seq R, by rw [hv] at hs0; exact hs0⟩

theorem checkPending_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_check_pending_event_spec d = some d1)
      (checkPendingH cidb ucb vb) (fun _ d _ d' => trap_check_pending_event_spec d = some d') :=
  reader_triple (ida := ida) εR c i0 hL (fun σ v r h => by
    obtain ⟨σ', S, hr, -⟩ := VVMCS.checkPending_step εR c i0 (hvb_of hL) (σ := σ) h; exact ⟨σ', S, hr⟩)

theorem checkIntShadow_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_check_int_shadow_spec d = some d1)
      (checkIntShadowH cidb ucb vb) (fun _ d _ d' => trap_check_int_shadow_spec d = some d') :=
  reader_triple (ida := ida) εR c i0 hL (fun σ v r h => by
    obtain ⟨σ', S, hr, -⟩ := VVMCS.checkIntShadow_step εR c i0 (hvb_of hL) (σ := σ) h; exact ⟨σ', S, hr⟩)

/-- **`sys_hvm_intercept_int_window` refines its specification.** -/
theorem intercept_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_intercept_int_window_spec d = some d1)
      (interceptH cidb ucb vb) (fun _ d _ d' => trap_intercept_int_window_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_intercept_int_window_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some en =>
    rw [e2] at hs; simp only at hs
    obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
    have A := argH (ida := ida) εR c i0 hL "enable" (by decide) (reg := U_EBX) (by decide) (σ := σ) hcp e2
    unfold intercept_int_window_x onV at hb
    cases hv : VVMCS.vmx_set_intercept_intwin_spec en (toV (toX d)) with
    | none => rw [hv] at hb; cases hb
    | some v =>
      rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨σ2, B⟩ := VVMCS.setIntwin_step εR c i0 (hvb_of hL) (F := fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) (fun k h1 h2 => ⟨h1, h2⟩)
        (σ := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "enable" (BitVec.ofNat 32 en)) (by simp)
        (arg_val e2).2 hv
      obtain ⟨σ3, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ2) (d := putX d { toX d with vmcs := v.vmcs }) hcp hR
      exact ⟨_, _, A.seq ((vH (ida := ida) εR c i0 hL B).seq R), hs0⟩

/-- **`sys_hvm_get_tsc_offset` refines its specification.** -/
theorem getTsc_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_get_tsc_offset_spec d = some d1)
      (getTscH cidb ucb vb) (fun _ d _ d' => trap_get_tsc_offset_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_get_tsc_offset_spec at hs
  obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
  unfold get_tsc_x at hb
  cases hv : VVMCS.vmcs_readz64_spec C_VMCS_TSC_OFFSET (toV (toX d)) with
  | none => rw [hv] at hb; cases hb
  | some p =>
    obtain ⟨lo, hi⟩ := p
    rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    let σ1 := σ.set "enc" (BitVec.ofNat 32 C_VMCS_TSC_OFFSET)
    have B := VVMCS.readz64_step εR c i0 (hvb_of hL) (F := fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC)
      (σ := σ1) (by simp [σ1]) hv
    obtain ⟨σ3, R, -⟩ := setsH (ida := ida) εR c i0 hL
      [(U_EBX, .var "hi", hi.toNat), (U_ECX, .var "lo", lo.toNat), (U_EAX, .const 0, 0)]
      ((σ1.set "lo" lo).set "hi" hi) (putX d (toX d)) u hcp
      (by
        intro p hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact ⟨by dsimp only; decide, fun τ hτ => by
            show τ "hi" = _; rw [hτ "hi" (by decide) (by decide)]; simp⟩
        · exact ⟨by dsimp only; decide, fun τ hτ => by
            show τ "lo" = _; rw [hτ "lo" (by decide) (by decide)]; simp [Locals.set]⟩
        · exact ⟨by dsimp only; decide, fun τ hτ => rfl⟩) hR
    exact ⟨_, _, (Step.assign "enc" (by decide) _).seq ((vH (ida := ida) εR c i0 hL B).seq R), hs0⟩

/-- **`sys_hvm_set_tsc_offset` refines its specification.** -/
theorem setTsc_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_set_tsc_offset_spec d = some d1)
      (setTscH cidb ucb vb) (fun _ d _ d' => trap_set_tsc_offset_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_set_tsc_offset_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some hi =>
    cases e3 : uctx_arg3_spec d.toUData with
    | none => rw [e2, e3] at hs; cases hs
    | some lo =>
      rw [e2, e3] at hs; simp only at hs
      obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
      have A1 := argH (ida := ida) εR c i0 hL "hi" (by decide) (reg := U_EBX) (by decide) (σ := σ) hcp e2
      have A2 := argH (ida := ida) εR c i0 hL "lo" (by decide) (reg := U_ECX) (by decide)
        (σ := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "hi" (BitVec.ofNat 32 hi)) hcp e3
      let σ2 := ((((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "hi" (BitVec.ofNat 32 hi)).set "curid"
        (BitVec.ofNat 32 d.cid)).set "lo" (BitVec.ofNat 32 lo)).set "enc" (BitVec.ofNat 32 C_VMCS_TSC_OFFSET)
      unfold set_tsc_x onV at hb
      cases hv : VVMCS.vmcs_writez64_spec C_VMCS_TSC_OFFSET (BitVec.ofNat 32 lo) (BitVec.ofNat 32 hi)
          (toV (toX d)) with
      | none => rw [hv] at hb; cases hb
      | some v =>
        rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have B := VVMCS.writez64_step εR c i0 (hvb_of hL) (F := fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) (fun k h1 h2 => ⟨h1, h2⟩) (σ := σ2)
          (by simp [σ2]) (by simp [σ2, Locals.set]) (by simp [σ2, Locals.set]) hv
        obtain ⟨σ3, R⟩ := errH (ida := ida) εR c i0 hL (σ := (σ2.set "_" 0).set "_" 0)
          (d := putX d { toX d with vmcs := v.vmcs }) hcp hR
        exact ⟨_, _, A1.seq (A2.seq ((Step.assign "enc" (by decide) _).seq ((vH (ida := ida) εR c i0 hL B).seq R))), hs0⟩

/-- **`sys_hvm_inject_event` refines its specification.** -/
theorem inject_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_inject_event_spec d = some d1)
      (injectH cidb ucb vb) (fun _ d _ d' => trap_inject_event_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_inject_event_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some ty =>
  cases e3 : uctx_arg3_spec d.toUData with
  | none => rw [e2, e3] at hs; cases hs
  | some ve =>
  cases e4 : uctx_arg4_spec d.toUData with
  | none => rw [e2, e3, e4] at hs; cases hs
  | some er =>
  cases e5 : uctx_arg5_spec d.toUData with
  | none => rw [e2, e3, e4, e5] at hs; cases hs
  | some ev =>
    rw [e2, e3, e4, e5] at hs; simp only at hs
    obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
    let cur := BitVec.ofNat 32 d.cid
    let σ1 := (σ.set "curid" cur).set "type" (BitVec.ofNat 32 ty)
    let σ2 := (σ1.set "curid" cur).set "vector" (BitVec.ofNat 32 ve)
    let σ3 := (σ2.set "curid" cur).set "errcode" (BitVec.ofNat 32 er)
    let σ4 := (σ3.set "curid" cur).set "ev" (BitVec.ofNat 32 ev)
    have A1 := argH (ida := ida) εR c i0 hL "type" (by decide) (reg := U_EBX) (by decide) (σ := σ) hcp e2
    have A2 := argH (ida := ida) εR c i0 hL "vector" (by decide) (reg := U_ECX) (by decide) (σ := σ1) hcp e3
    have A3 := argH (ida := ida) εR c i0 hL "errcode" (by decide) (reg := U_EDX) (by decide) (σ := σ2) hcp e4
    have A4 := argH (ida := ida) εR c i0 hL "ev" (by decide) (reg := U_ESI) (by decide) (σ := σ3) hcp e5
    unfold inject_event_x onV at hb
    cases hv : VVMCS.vmx_inject_event_spec (BitVec.ofNat 32 ty) (BitVec.ofNat 32 ve) (BitVec.ofNat 32 er) ev
        (toV (toX d)) with
    | none => rw [hv] at hb; cases hb
    | some v =>
      rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨σ5, B⟩ := VVMCS.injectEvent_step εR c i0 (hvb_of hL) (F := fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) (fun k h1 h2 => ⟨h1, h2⟩) (σ := σ4)
        (by simp [σ4, σ3, σ2, σ1, cur, Locals.set]) (by simp [σ4, σ3, σ2, σ1, cur, Locals.set]) (by simp [σ4, σ3, σ2, σ1, cur, Locals.set])
        (by simp [σ4, σ3, σ2, σ1, cur, Locals.set]) (arg_val e5).2 hv
      obtain ⟨σ6, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ5) (d := putX d { toX d with vmcs := v.vmcs }) hcp hR
      exact ⟨_, _, A1.seq (A2.seq (A3.seq (A4.seq ((vH (ida := ida) εR c i0 hL B).seq R)))), hs0⟩

/-- **`sys_hvm_set_seg` refines its specification.** -/
theorem setSeg_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_set_seg_spec d = some d1)
      (setSegH cidb ucb vb) (fun _ d _ d' => trap_set_seg_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_set_seg_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some seg =>
  cases e3 : uctx_arg3_spec d.toUData with
  | none => rw [e2, e3] at hs; cases hs
  | some sel =>
  cases e4 : uctx_arg4_spec d.toUData with
  | none => rw [e2, e3, e4] at hs; cases hs
  | some base =>
  cases e5 : uctx_arg5_spec d.toUData with
  | none => rw [e2, e3, e4, e5] at hs; cases hs
  | some lim =>
  cases e6 : uctx_arg6_spec d.toUData with
  | none => rw [e2, e3, e4, e5, e6] at hs; cases hs
  | some ar =>
    rw [e2, e3, e4, e5, e6] at hs; simp only at hs
    obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
    let cur := BitVec.ofNat 32 d.cid
    let σ1 := (σ.set "curid" cur).set "seg" (BitVec.ofNat 32 seg)
    let σ2 := (σ1.set "curid" cur).set "sel" (BitVec.ofNat 32 sel)
    let σ3 := (σ2.set "curid" cur).set "base" (BitVec.ofNat 32 base)
    let σ4 := (σ3.set "curid" cur).set "lim" (BitVec.ofNat 32 lim)
    let σ5 := (σ4.set "curid" cur).set "ar" (BitVec.ofNat 32 ar)
    have A1 := argH (ida := ida) εR c i0 hL "seg" (by decide) (reg := U_EBX) (by decide) (σ := σ) hcp e2
    have A2 := argH (ida := ida) εR c i0 hL "sel" (by decide) (reg := U_ECX) (by decide) (σ := σ1) hcp e3
    have A3 := argH (ida := ida) εR c i0 hL "base" (by decide) (reg := U_EDX) (by decide) (σ := σ2) hcp e4
    have A4 := argH (ida := ida) εR c i0 hL "lim" (by decide) (reg := U_ESI) (by decide) (σ := σ3) hcp e5
    have A5 := argH (ida := ida) εR c i0 hL "ar" (by decide) (reg := U_EDI) (by decide) (σ := σ4) hcp e6
    have hseg : σ5 "seg" = BitVec.ofNat 32 seg := by simp [σ5, σ4, σ3, σ2, σ1, cur, Locals.set]
    have hg := guard_lt (σ := σ5) (x := "seg") (a := seg) (b := 10) hseg (arg_val e2).2 (by decide)
    unfold set_seg_x at hb
    by_cases t : seg < 10
    · rw [if_pos t] at hb hg
      unfold onV at hb
      cases hv : VVMCS.vmx_set_desc_spec seg (BitVec.ofNat 32 sel) (BitVec.ofNat 32 base) (BitVec.ofNat 32 lim)
          (BitVec.ofNat 32 ar) (toV (toX d)) with
      | none => rw [hv] at hb; cases hb
      | some v =>
        rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨σ6, B⟩ := VVMCS.setDesc_step εR c i0 (hvb_of hL) (F := fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) (fun k h1 h2 => ⟨h1, h2⟩) (σ := σ5) hseg
          (by simp [σ5, σ4, σ3, σ2, σ1, cur, Locals.set]) (by simp [σ5, σ4, σ3, σ2, σ1, cur, Locals.set]) (by simp [σ5, σ4, σ3, σ2, σ1, cur, Locals.set])
          (by simp [σ5, σ4, σ3, σ2, σ1, cur, Locals.set]) hv
        obtain ⟨σ7, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ6) (d := putX d { toX d with vmcs := v.vmcs }) hcp hR
        exact ⟨_, _, A1.seq (A2.seq (A3.seq (A4.seq (A5.seq (Step.ite_true (fun h => absurd (hg.symm.trans h) (by decide))
          ((vH (ida := ida) εR c i0 hL B).seq R)))))), hs0⟩
    · rw [if_neg t] at hb hg
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨σ7, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ5) (d := putX d (toX d)) hcp hR
      exact ⟨_, _, A1.seq (A2.seq (A3.seq (A4.seq (A5.seq (Step.ite_false (by exact hg) R))))), hs0⟩

end Steps

end TTop
