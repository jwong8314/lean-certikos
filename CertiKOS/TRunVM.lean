import CertiKOS.THyp3
import CertiKOS.GMachine

/-!
# `SYS_hvm_run_vm`: entering the guest and coming back

In mCertiKOS, running the virtual machine is not a row of the dispatcher: like
`sys_yield`, it is its own path through the trap layer (`TSysCall.v`:
`vmx_enter`, `vmx_return_from_guest`), because it leaves the kernel by a VM
entry rather than by `iret`. Here:

* `run_vm_spec`: `vm_run_spec` on the top state; the processor is then in
  guest mode (`ihost = false`).
* `runVmS`: `vm_run(); GUEST = 1;`. The machine (`GMachine`) enters the guest
  when a kernel computation ends with `GUEST` set.
* `exit_spec`, `exitS`: the VM exit handler: `vmx_return_from_guest(); ihost
  = true; uctx_set_errno(E_SUCC); GUEST = 0;`, and the machine returns to the
  caller in user mode.
* `run_vm_enters`: **from the kernel, `SYS_hvm_run_vm` reaches guest mode
  with the guest's registers** (those in the `vmx` structure).
* `vm_exit_returns`: **from guest mode, a VM exit reaches the caller in user
  mode**, with the host's `edi` and `ebp` back and the region matching the
  specification.

What differs: the host registers `vm_run` saves are the kernel's locals `EBP`
and `EDI` at the call, as in `VVMX`.
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
open MALOp MPTIntro PUCtxt TTrap KMach UMach GMach
open VVMX (XSt MatchX XF)
open MALInit (asg_run)

def run_vm_spec (rebp redi : Val) (d : HData) : Option HData :=
  match VVMX.vm_run_spec rebp redi (toX d) with
  | some x => some { putX d x with ihost := false }
  | none => none

def exit_spec (redi reax rebx redx resi rebp : Val) (d : HData) : Option HData :=
  match VVMX.vmx_return_from_guest_spec redi reax rebx redx resi rebp (toX d) with
  | some x => hcall (some (x, [(U_EAX, 0)])) { d with ihost := true }
  | none => none

def runVmS (xb vb : Nat) : Stmt APrim := .seq (VVMX.vmRunS xb vb) (.assign "GUEST" (.const 1))

def exitS (cidb ucb xb vb : Nat) : Stmt APrim :=
  .seq (VVMX.returnS xb vb) (.seq (errS cidb ucb 0) (.assign "GUEST" (.const 0)))

section Run
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

theorem run_ept {r1 r2 : Val} {x x' : XSt} (h : VVMX.vm_run_spec r1 r2 x = some x') : VEPT.SameShape x.ept x'.ept := by
  apply VEPT.SameShape.of_eq
  unfold VVMX.vm_run_spec at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

theorem return_ept {a b c' dx si bp : Val} {x x' : XSt} (h : VVMX.vmx_return_from_guest_spec a b c' dx si bp x = some x') :
    VEPT.SameShape x.ept x'.ept := by
  apply VEPT.SameShape.of_eq
  unfold VVMX.vmx_return_from_guest_spec at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

/-- The region does not see `ihost`. -/
theorem matchH_ihost {d : HData} {b : Region} (v : Bool) (h : MH d b) : MH { d with ihost := v } b := h

/-- **`SYS_hvm_run_vm` enters the guest** with the registers of the `vmx`
structure. -/
theorem run_vm_enters (hL : HL) (code : Nat → Stmt KPrim) (entry : Nat → Nat) (exitEntry : Nat) (lk : Val)
    {σ : Locals} {d d' : HData} {l : RLog} {b : Region} {pool : Nat → KCtx} {a bx dx si di bp ip : Val}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MH d b)
    (ha : d.vmx VVMX.VMX_G_RAX' = some a) (hbx : d.vmx VVMX.VMX_G_RBX' = some bx)
    (hdx : d.vmx VVMX.VMX_G_RDX' = some dx) (hsi : d.vmx VVMX.VMX_G_RSI' = some si)
    (hdi : d.vmx VVMX.VMX_G_RDI' = some di) (hbp : d.vmx VVMX.VMX_G_RBP' = some bp)
    (hip : d.vmx VVMX.VMX_G_RIP' = some ip) (hs : run_vm_spec (σ "EBP") (σ "EDI") d = some d') :
    ∃ gr l' b', GStar εR c code entry exitEntry lk (.kern ⟨⟨mapS .base (runVmS xb vb), .stop, σ⟩, pool, l⟩)
        (.guest gr pool l') ∧ CS1 c i0 l' b' ∧ MH d' b' ∧
      gr 0 = a ∧ gr 1 = bx ∧ gr 2 = dx ∧ gr 3 = si ∧ gr 4 = di ∧ gr 5 = bp ∧ gr 6 = ip := by
  unfold run_vm_spec at hs
  cases hx : VVMX.vm_run_spec (σ "EBP") (σ "EDI") (toX d) with
  | none => rw [hx] at hs; cases hs
  | some x =>
    rw [hx] at hs; simp only [Option.some.injEq] at hs; subst hs
    obtain ⟨σ1, S, e0, e1, e2, e3, e4, e5, e6⟩ := VVMX.vmRun_step hL.hxv hL.hve (heb_of hL) εR c i0
      (σ := σ) rfl rfl ha hbx hdx hsi hdi hbp hip hx
    have S' : Step εR c i0 MH (HF ucb num_proc xb vb eb) (runVmS xb vb) σ d (σ1.set "GUEST" 1)
        { putX d x with ihost := false } :=
      (VVMX.Step.post (xH (ida := ida) εR c i0 hL S (run_ept hx)) (fun b h => matchH_ihost false h)).seq
        (Step.assign "GUEST" (by decide) (.const 1))
    obtain ⟨l1, b1, r1, c1, m1, -⟩ := S'.2 l b hlk hcs hM
    refine ⟨gregsOf (σ1.set "GUEST" 1), l1, b1, GStar.vmenter (KStar.of_runs r1 .stop pool) (by simp),
      c1, m1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [gregsOf, gname, Locals.set, *]

/-- **A VM exit returns to the caller in user mode**: the exit handler saves
the guest's registers, puts the host's `edi` and `ebp` back, and sets the
caller's error code. -/
theorem vm_exit_returns (hL : HL) (code : Nat → Stmt KPrim) (entry : Nat → Nat) (exitEntry : Nat) (lk : Val)
    (hcode : code exitEntry = mapS .base (exitS cidb ucb xb vb)) {gr : Nat → Val} {σ : Locals} {d d' : HData}
    {l : RLog} {b : Region} {pool : Nat → KCtx} {he hb : Val}
    (hlk : σ "lk" = lk) (hlk' : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MH d b) (hcp : d.cid < num_proc)
    (hhe : d.vmx VVMX.VMX_HOST_EDI' = some he) (hhb : d.vmx VVMX.VMX_HOST_EBP' = some hb)
    (hs : exit_spec (σ "EDI") (σ "EAX") (σ "EBX") (σ "EDX") (σ "ESI") (σ "EBP") d = some d') :
    ∃ σ' l' b', GStar εR c code entry exitEntry lk (.guest gr pool l) (.user (regsOf σ') pool l') ∧
      CS1 c i0 l' b' ∧ MH d' b' ∧ σ' "EDI" = he ∧ σ' "EBP" = hb := by
  unfold exit_spec at hs
  cases hx : VVMX.vmx_return_from_guest_spec (σ "EDI") (σ "EAX") (σ "EBX") (σ "EDX") (σ "ESI") (σ "EBP") (toX d) with
  | none => rw [hx] at hs; cases hs
  | some x =>
    rw [hx] at hs; simp only at hs
    obtain ⟨x', o, u, hb', hR, rfl⟩ := hcall_some hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    obtain ⟨σ1, S, e1, e2⟩ := VVMX.return_step hL.hxv hL.hve (heb_of hL) εR c i0 (σ := σ) rfl rfl rfl rfl rfl rfl
      hhe hhb hx
    have S1 : Step εR c i0 MH (HF ucb num_proc xb vb eb) (VVMX.returnS xb vb) σ d σ1
        (putX { d with ihost := true } x) :=
      VVMX.Step.post (xH (ida := ida) εR c i0 hL S (return_ept hx)) (fun b h => h)
    obtain ⟨σ2, R⟩ := errH (ida := ida) (cidb := cidb) εR c i0 hL (σ := σ1) (d := putX { d with ihost := true } x)
      hcp hR
    obtain ⟨l1, b1, r1, c1, m1, -⟩ := S1.2 l b hlk' hcs hM
    obtain ⟨l2, b2, r2, c2, m2, -⟩ := R.2 l1 b1 (by rw [S1.1]; exact hlk') c1 m1
    have r3 : Runs (rprimsA εR c) (.assign "GUEST" (.const 0)) σ2 l2 (σ2.set "GUEST" 0) l2 :=
      asg_run "GUEST" (.const 0) rfl
    have rAll : Runs (rprimsA εR c) (exitS cidb ucb xb vb) σ l (σ2.set "GUEST" 0) l2 :=
      Runs.seq r1 (Runs.seq r2 r3)
    have hrun := KStar.of_runs (εR := εR) (c := c) (code := code) rAll .stop pool
    rw [← hcode] at hrun
    have k2 : ∀ z, z = "EDI" ∨ z = "EBP" → σ2 z = σ1 z := by
      rintro z (rfl | rfl) <;> exact r2.frame rfl
    refine ⟨σ2.set "GUEST" 0, l2, b2, GStar.exit_to_user hlk hrun (by simp), c2, m2, ?_, ?_⟩
    · rw [Locals.set_other _ _ (by decide), k2 _ (by simp), e1]
    · rw [Locals.set_other _ _ (by decide), k2 _ (by simp), e2]

end Run

end TTop
