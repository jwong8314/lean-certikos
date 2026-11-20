import CertiKOS.PProc

/-!
# mCertiKOS `TTrapArg`: system-call arguments, ported

A system call's arguments are registers of the caller's user context, and so
are its error code and return values.

Ported from `objects/ObjArg.v`: `uctx_arg1_spec` … `uctx_arg6_spec`,
`uctx_set_errno_spec`, `uctx_set_retval1_spec` … `uctx_set_retval5_spec`.
Ported from `trap/PProcCSource.v`: the C code, which is `get_curid` followed
by `uctx_get` or `uctx_set`.

* `uctx_arg_spec reg`, `uctx_set_reg_spec reg`: the specifications, with the
  register as a parameter; mCertiKOS's twelve are instances (`uctx_arg1_spec`
  reads `EAX`, the system-call number; `uctx_set_errno_spec` writes `EAX`).
* `uctxArgU`, `uctxSetRegU`: the code as steps on the top state.
* `uctxArg_triple`, `uctxSetReg_triple`: **the code refines the
  specifications.**

What differs: the theorems assume the current thread is below `num_proc`
(mCertiKOS's `valid_curid`), which `uctx_get` needs.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TTrap

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Specifications (`ObjArg.v`) -/

/-- Register `reg` of the current process's user context. -/
def uctx_arg_spec (reg : Nat) (d : UData) : Option Nat :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true then
    match d.uctxt d.cid reg with
    | some n => some n.toNat
    | none => none
  else none

/-- The system-call number. -/
def uctx_arg1_spec := uctx_arg_spec U_EAX
def uctx_arg2_spec := uctx_arg_spec U_EBX
def uctx_arg3_spec := uctx_arg_spec U_ECX
def uctx_arg4_spec := uctx_arg_spec U_EDX
def uctx_arg5_spec := uctx_arg_spec U_ESI
def uctx_arg6_spec := uctx_arg_spec U_EDI

/-- Write register `reg` of the current process's user context. -/
def uctx_set_reg_spec (reg n : Nat) (d : UData) : Option UData :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true then
    some { d with uctxt := setAt d.uctxt d.cid (setAt (d.uctxt d.cid) reg (some (BitVec.ofNat 32 n))) }
  else none

/-- The error code of a system call. -/
def uctx_set_errno_spec := uctx_set_reg_spec U_EAX
def uctx_set_retval1_spec := uctx_set_reg_spec U_EBX
def uctx_set_retval2_spec := uctx_set_reg_spec U_ECX
def uctx_set_retval3_spec := uctx_set_reg_spec U_EDX
def uctx_set_retval4_spec := uctx_set_reg_spec U_ESI
def uctx_set_retval5_spec := uctx_set_reg_spec U_EDI

def E_SUCC : Nat := 0
def E_MEM : Nat := 1
def E_INVAL_CALLNR : Nat := 3

/-! ## The C code (`PProcCSource.v`) -/

/-- `x = uctx_argN()`: `curid = get_curid(); x = uctx_get(curid, reg);` -/
def uctxArgS (cidb ucb : Nat) (x : Ident) (reg : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "curid") (uctxGetS ucb x (.var "curid") (.const (BitVec.ofNat 32 reg)))

/-- `uctx_set_errno(v)`, `uctx_set_retvalN(v)`:
`curid = get_curid(); uctx_set(curid, reg, v);` -/
def uctxSetRegS (cidb ucb reg : Nat) (ve : Expr) : Stmt APrim :=
  .seq (getCuridS cidb "curid") (uctxSetS ucb (.var "curid") (.const (BitVec.ofNat 32 reg)) ve)

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb

/-- Reading an argument that is known. -/
theorem uctxArgU (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb) (x : Ident)
    (hx : x ≠ "lk") {reg : Nat} (hreg : reg < 17) {σ : Locals} {d : UData} {v : Val}
    (hcid : d.cid < num_proc) (hv : d.uctxt d.cid reg = some v) :
    Step εR c i0 MU F (uctxArgS cidb ucb x reg) σ d ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set x v) d :=
  Step.seq (getCuridU εR c i0 hL "curid" (by decide) σ d)
    (uctxGetU εR c i0 hL x hx (ie := .var "curid") (oe := .const (BitVec.ofNat 32 reg)) (by simp [Expr.eval])
      rfl hcid hreg hv)

/-- Writing a register of the caller. -/
theorem uctxSetRegU (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hF : ∀ k, UCF ucb num_proc k → F k) {reg : Nat} (hreg : reg < 17) {ve : Expr} {σ : Locals} {d : UData}
    {w : Val} (hve : ve.eval (σ.set "curid" (BitVec.ofNat 32 d.cid)) = w) (hcid : d.cid < num_proc) :
    Step εR c i0 MU F (uctxSetRegS cidb ucb reg ve) σ d ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "_" 0)
      { d with uctxt := setAt d.uctxt d.cid (setAt (d.uctxt d.cid) reg (some w)) } :=
  Step.seq (getCuridU εR c i0 hL "curid" (by decide) σ d)
    (uctxSetU εR c i0 hL hF (ie := .var "curid") (oe := .const (BitVec.ofNat 32 reg)) (by simp [Expr.eval]) rfl
      hve hcid hreg)

/-- **`uctx_argN` refines `uctx_arg_spec`.** -/
theorem uctxArg_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (x : Ident) (hx : x ≠ "lk") (reg : Nat) (hreg : reg < 17) :
    Triple εR c i0 MU (fun _ => False)
      (fun _ d => d.cid < num_proc ∧ ∃ v, uctx_arg_spec reg d = some v)
      (uctxArgS cidb ucb x reg)
      (fun σ d σ' d' => d' = d ∧ ∃ v, uctx_arg_spec reg d = some v ∧
        σ' = (σ.set "curid" (BitVec.ofNat 32 d.cid)).set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨hcid, v, hs⟩ => ?_)
  have hs0 := hs
  unfold uctx_arg_spec at hs
  split at hs
  · cases hu : d.uctxt d.cid reg with
    | none => rw [hu] at hs; cases hs
    | some w =>
      rw [hu] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, d, uctxArgU εR c i0 hL x hx hreg hcid hu, rfl, _, hs0, by simp⟩
  · cases hs

/-- **`uctx_set_errno` and `uctx_set_retvalN` refine `uctx_set_reg_spec`.** -/
theorem uctxSetReg_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (reg : Nat) (hreg : reg < 17) (ve : Expr) (n : Nat) :
    Triple εR c i0 MU (UCF ucb num_proc)
      (fun σ d => d.cid < num_proc ∧ ve.eval (σ.set "curid" (BitVec.ofNat 32 d.cid)) = BitVec.ofNat 32 n ∧
        ∃ d1, uctx_set_reg_spec reg n d = some d1)
      (uctxSetRegS cidb ucb reg ve)
      (fun σ d σ' d' => uctx_set_reg_spec reg n d = some d' ∧
        σ' = (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "_" 0) := by
  refine Step.triple (fun σ d ⟨hcid, hve, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold uctx_set_reg_spec at hs
  split at hs
  · simp only [Option.some.injEq] at hs
    subst hs
    exact ⟨_, _, uctxSetRegU εR c i0 hL (fun _ h => h) hreg hve hcid, hs0, rfl⟩
  · cases hs

end Code

end TTrap
