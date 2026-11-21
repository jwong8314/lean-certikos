import CertiKOS.THLock2
import CertiKOS.TRunVM

/-!
# `SYS_hvm_run_vm` with the lock

`TRunVM` runs the virtual machine on the machine with guest mode
(`GMachine`): `run_vm_enters` from the kernel to guest mode,
`vm_exit_returns` from a VM exit to the caller in user mode. Neither was an
entry point with the lock and the invariant. Here they are.

In mCertiKOS `sys_run_vm` is `proc_exit_user; jmp vmx_run_vm`, and its entry
in the trap layer is commented out (`TSysCall.v`): it was never verified. The
port keeps the code of `TRunVM` (`runVmS`, `exitS`).

**Where the lock is.** The trap acquires the lock, runs `vm_run` and enters
the guest **still holding it**; the VM exit handler runs
`vmx_return_from_guest`, releases the lock and returns to the caller:

```
trap:     acquire(lk); vm_run(); GUEST = 1;            -- VM entry
VM exit:  vmx_return_from_guest(); ...; GUEST = 0; release(lk);   -- iret
```

The processor's mode (`ihost`) is per-CPU state, of which the machine has one
copy, and while the guest runs it is `false`, which `KInv` excludes. Releasing
the lock before the VM entry would put a state with `ihost = false` on the
log, where another CPU's trap would find it. Holding the lock across guest
mode makes the guest part of the critical section, so `GoodH` is all the log
ever shows. The cost is liveness: no other CPU enters the kernel while a
guest runs (the fairness of the lock assumes bounded critical sections).

* `setRegs_shapeH`, `run_vm_shape`, `exit_shape'`: the shapes of the specs.
* `runVm_runs`, `exit_runs`: the two pieces of code as runs, with their
  footprints.
* `run_vm_h_locked`: **from user mode, `SYS_hvm_run_vm` enters the guest
  with the lock held, and every VM exit after it returns to the caller with
  the lock released and `GoodH` on the log.**
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
open LockArray (AEnv ALog acquireA apull)
open LockRegion (RState HLogR rreplay hmemR)
open LogInv TSysCall TInv TLock

/-! ## Shapes -/

theorem setRegs_shapeH : ∀ (o : List (Nat × Nat)) (u u' : UData), setRegs o u = some u' →
    ∃ U, u' = { u with uctxt := U }
  | [], u, u', h => by
    simp only [setRegs, Option.some.injEq] at h
    subst h; exact ⟨u.uctxt, rfl⟩
  | (r, n) :: t, u, u', h => by
    simp only [setRegs] at h
    cases h1 : uctx_set_reg_spec r n u with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h
      obtain ⟨U1, e1⟩ := set_reg_shape h1
      obtain ⟨U, e⟩ := setRegs_shapeH t u1 u' h
      exact ⟨U, by rw [e, e1]⟩

theorem run_vm_shape {r1 r2 : Val} {d d' : HData} (h : run_vm_spec r1 r2 d = some d') :
    ∃ x, d' = { putX d x with ihost := false } := by
  unfold run_vm_spec at h
  cases hx : VVMX.vm_run_spec r1 r2 (toX d) with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; simp only [Option.some.injEq] at h; exact ⟨x, h.symm⟩

theorem exit_shape' {a b c' dx si bp : Val} {d d' : HData} (h : exit_spec a b c' dx si bp d = some d') :
    ∃ x U, d' = { putX { d with ihost := true } x with toUData :=
      { (putX { d with ihost := true } x).toUData with uctxt := U } } := by
  unfold exit_spec at h
  cases hx : VVMX.vmx_return_from_guest_spec a b c' dx si bp (toX d) with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h; simp only at h
    obtain ⟨x', o, u, hb', hR, rfl⟩ := hcall_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    obtain ⟨U, e⟩ := setRegs_shapeH _ _ _ hR
    exact ⟨_, U, by rw [e]⟩

/-! ## The two pieces of code as runs -/

section Runs
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- **`vm_run(); GUEST = 1;` as a run**, with the guest's registers left in
the locals. -/
theorem runVm_runs (hL : HL) {σ : Locals} {d d' : HData} {l : RLog} {b : Region} {a bx dx si di bp ip : Val}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MH d b)
    (ha : d.vmx VVMX.VMX_G_RAX' = some a) (hbx : d.vmx VVMX.VMX_G_RBX' = some bx)
    (hdx : d.vmx VVMX.VMX_G_RDX' = some dx) (hsi : d.vmx VVMX.VMX_G_RSI' = some si)
    (hdi : d.vmx VVMX.VMX_G_RDI' = some di) (hbp : d.vmx VVMX.VMX_G_RBP' = some bp)
    (hip : d.vmx VVMX.VMX_G_RIP' = some ip) (hs : run_vm_spec (σ "EBP") (σ "EDI") d = some d') :
    ∃ σ' l' b', Runs (rprimsA εR c) (runVmS xb vb) σ l σ' l' ∧ CS1 c i0 l' b' ∧ MH d' b' ∧
      (∀ k, ¬ HF ucb num_proc xb vb eb k → b' k = b k) ∧ σ' "lk" = σ "lk" ∧ σ' "GUEST" ≠ 0 ∧
      gregsOf σ' 0 = a ∧ gregsOf σ' 1 = bx ∧ gregsOf σ' 2 = dx ∧ gregsOf σ' 3 = si ∧ gregsOf σ' 4 = di ∧
      gregsOf σ' 5 = bp ∧ gregsOf σ' 6 = ip := by
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
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := S'.2 l b hlk hcs hM
    refine ⟨σ1.set "GUEST" 1, l1, b1, r1, c1, m1, f1, S'.1, by simp [Locals.set], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [gregsOf, gname, Locals.set, *]

/-- **The VM exit handler as a run**: the host's `edi` and `ebp` back,
`GUEST` cleared. -/
theorem exit_runs (hL : HL) {σ : Locals} {d d' : HData} {l : RLog} {b : Region} {he hb : Val}
    (hlk' : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MH d b) (hcp : d.cid < num_proc)
    (hhe : d.vmx VVMX.VMX_HOST_EDI' = some he) (hhb : d.vmx VVMX.VMX_HOST_EBP' = some hb)
    (hs : exit_spec (σ "EDI") (σ "EAX") (σ "EBX") (σ "EDX") (σ "ESI") (σ "EBP") d = some d') :
    ∃ σ' l' b', Runs (rprimsA εR c) (exitS cidb ucb xb vb) σ l σ' l' ∧ CS1 c i0 l' b' ∧ MH d' b' ∧
      (∀ k, ¬ HF ucb num_proc xb vb eb k → b' k = b k) ∧ σ' "lk" = σ "lk" ∧ σ' "GUEST" = 0 ∧
      σ' "EDI" = he ∧ σ' "EBP" = hb := by
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
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := S1.2 l b hlk' hcs hM
    obtain ⟨l2, b2, r2, c2, m2, f2⟩ := R.2 l1 b1 (by rw [S1.1]; exact hlk') c1 m1
    have r3 : Runs (rprimsA εR c) (.assign "GUEST" (.const 0)) σ2 l2 (σ2.set "GUEST" 0) l2 :=
      asg_run "GUEST" (.const 0) rfl
    have k2 : ∀ z, z = "EDI" ∨ z = "EBP" → σ2 z = σ1 z := by
      rintro z (rfl | rfl) <;> exact r2.frame rfl
    refine ⟨σ2.set "GUEST" 0, l2, b2, Runs.seq r1 (Runs.seq r2 r3), c2, m2,
      fun k hk => by rw [f2 k hk, f1 k hk], ?_, by simp [Locals.set], ?_, ?_⟩
    · rw [Locals.set_other _ _ (by decide), R.1, S1.1]
    · rw [Locals.set_other _ _ (by decide), k2 _ (by simp), e1]
    · rw [Locals.set_other _ _ (by decide), k2 _ (by simp), e2]

end Runs

/-! ## The entry point with the lock -/

/-- The VM exit keeps `KInv`, once the processor is back in the host. -/
theorem exit_kinv {num_id mc num_proc num_chan maxpage kl kh : Nat} {a b c' dx si bp : Val} {d d'' : HData}
    (h : exit_spec a b c' dx si bp d = some d'')
    (hI : KInv num_id mc num_proc num_chan maxpage kl kh ({ d with ihost := true } : HData).toUData) :
    KInv num_id mc num_proc num_chan maxpage kl kh d''.toUData := by
  unfold exit_spec at h
  cases hx : VVMX.vmx_return_from_guest_spec a b c' dx si bp (toX d) with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; exact hcall_keeps h hI

section Locked
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub elb mc kl kh
  pstart : Nat}
variable {elf : Nat → Nat} {code : Nat → Stmt KPrim} {lk : Val}

local notation "GH" => GoodH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub
  elb mc kl kh pstart elf code lk
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- **`SYS_hvm_run_vm` with the lock.** From user mode, on a log whose last
released region is `GoodH`, the trap acquires the lock and, for any `GoodH`
state found there for which `run_vm_spec` is defined, enters the guest with
the guest's registers, the lock held. Then whatever registers the guest has
at a VM exit, the exit handler returns to the caller in user mode with the
host's `edi` and `ebp`, the lock released and idle, and the last released
region `GoodH` for the state `exit_spec` gives. -/
theorem run_vm_h_locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU)
    (hRA : LockArray.RelyA ε c) (entry : Nat → Nat) (tn exitEntry : Nat) (hL : HL)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub)
    (hentry : code (entry tn) = .seq (mapS .base acquireA) (mapS .base (runVmS xb vb)))
    (hexit : code exitEntry = .seq (mapS .base (exitS cidb ucb xb vb)) (mapS .base relA))
    {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hidle : (S.lk lk.toNat).phase c = .idle)
    (bound : ALog → Nat) (Kb : Nat) (hK : ∀ l, bound l ≤ Kb)
    (hF : LockArray.FairA ε c lk.toNat (ticket (LockArray.projL lk.toNat (apull ε c (erase l)))) bound)
    {pool : Nat → KCtx} (hRJ : RelyJ εR c lk.toNat (fun b => ∃ d, GH d b ∧ d.kctxt = pool))
    (hJ : ∃ d, GH d (hmemR lk.toNat H) ∧ d.kctxt = pool) (ur0 : Nat → Val) (σ : Locals) (hσ : σ "lk" = lk) :
    ∃ H1 : HLogR, (∃ d, GH d (hmemR lk.toNat H1) ∧ d.kctxt = pool) ∧
      ∀ (d d' : HData) (a bx dx si di bp ip : Val), GH d (hmemR lk.toNat H1) → d.kctxt = pool →
        d.vmx VVMX.VMX_G_RAX' = some a → d.vmx VVMX.VMX_G_RBX' = some bx →
        d.vmx VVMX.VMX_G_RDX' = some dx → d.vmx VVMX.VMX_G_RSI' = some si →
        d.vmx VVMX.VMX_G_RDI' = some di → d.vmx VVMX.VMX_G_RBP' = some bp →
        d.vmx VVMX.VMX_G_RIP' = some ip → run_vm_spec (σ "EBP") (σ "EDI") d = some d' →
        ∃ (gr : Nat → Val) (l1 : RLog),
          GStar εR c code entry exitEntry lk (.user ur0 pool l) (.guest gr pool l1) ∧
          gr 0 = a ∧ gr 1 = bx ∧ gr 2 = dx ∧ gr 3 = si ∧ gr 4 = di ∧ gr 5 = bp ∧ gr 6 = ip ∧
          ∀ (gr' : Nat → Val) (σx : Locals) (d'' : HData) (he hb : Val), σx "lk" = lk →
            d'.vmx VVMX.VMX_HOST_EDI' = some he → d'.vmx VVMX.VMX_HOST_EBP' = some hb →
            exit_spec (σx "EDI") (σx "EAX") (σx "EBX") (σx "EDX") (σx "ESI") (σx "EBP") d' = some d'' →
            ∃ (σ' : Locals) (l' : RLog) (S' : RState) (H' : HLogR),
              GStar εR c code entry exitEntry lk (.guest gr' pool l1) (.user (regsOf σ') pool l') ∧
              rreplay l' = some (S', H') ∧ (S'.lk lk.toNat).phase c = .idle ∧
              GH d'' (hmemR lk.toNat H') ∧ d''.kctxt = pool ∧ σ' "EDI" = he ∧ σ' "EBP" = hb := by
  have hU := hL.ulay
  have hCL := hU.ilay.clay
  have := hU.hub0; have := hU.hue; have := hU.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve
  -- the cells below the user contexts are outside the footprint of both pieces
  have nHF : ∀ k, k < ucb → ¬ HF ucb num_proc xb vb eb k := by
    intro k hk h
    rcases h with h | (h | h | h)
    · unfold UCF at h; omega
    all_goals omega
  obtain ⟨σ1, r1, H1, hacq, hcs1, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound Kb hK hF σ hσ
  refine ⟨H1, hJ1, fun d d' a bx dx si di bp ip hG hpool ha hbx hdx hsi hdi hbp hip hs => ?_⟩
  obtain ⟨hM, hE1, hI, hik, hP⟩ := hG
  have hs1 : run_vm_spec (σ1 "EBP") (σ1 "EDI") d = some d' := by
    rw [hfr "EBP" (by decide) (by decide) (by decide) (by decide),
      hfr "EDI" (by decide) (by decide) (by decide) (by decide)]
    exact hs
  obtain ⟨σ2, l1, b1, rv, c1, m1, f1, k1, hg1, g0, g1, g2, g3, g4, g5, g6⟩ :=
    runVm_runs (ida := ida) (cidb := cidb) εR c lk.toNat hL (σ := σ1) (by rw [hlk1]) hcs1 (matchHP_H hM)
      ha hbx hdx hsi hdi hbp hip hs1
  obtain ⟨x1, rfl⟩ := run_vm_shape hs
  refine ⟨gregsOf σ2, l1, ?_, g0, g1, g2, g3, g4, g5, g6, fun gr' σx d'' he hb hσx hhe hhb hx => ?_⟩
  · refine .step (.trap ur0 pool l tn σ hσ) ?_
    rw [hentry]
    exact GStar.vmenter ((kstar_seq hacq _ .stop pool).trans (KStar.of_runs rv .stop pool)) hg1
  · obtain ⟨σ3, l2, b2, rx, c2, m2, f2, k2, hg2, hdi', hbp'⟩ :=
      exit_runs (ida := ida) (cidb := cidb) εR c lk.toNat hL (σ := σx) (by rw [hσx]) c1 m1 hI.cid hhe hhb hx
    obtain ⟨rb, S3, H3, hrel, hl3, hid3, hmem⟩ := release_runs (εR := εR) hRR hc c2 (k2.trans hσx)
    have hK2 := exit_kinv (num_id := num_id) (mc := mc) (num_chan := num_chan) (maxpage := maxpage) (kl := kl)
      (kh := kh) hx ⟨hI.cid, hI.cur, hI.ainv, hI.cv, hI.atinv, hI.uq, hI.pg, rfl, hI.init⟩
    obtain ⟨x2, U, rfl⟩ := exit_shape' hx
    have fb : ∀ k, k < ucb → b2 k = hmemR lk.toNat H1 k := fun k hk => by
      rw [f2 k (nHF k hk), f1 k (nHF k hk)]
    refine ⟨σ3.set "_" 0, rb, S3, H3, ?_, hl3, hid3, ⟨?_, ?_, ?_, hik, hP.congr rfl rfl rfl⟩, hpool, ?_, ?_⟩
    · have h := (kstar_seq (code := code) rx _ .stop pool).trans (kstar_base hrel .stop pool)
      rw [← hexit] at h
      exact GStar.exit_to_user hσx h (by rw [Locals.set_other _ _ (by decide)]; exact hg2)
    · rw [hmem]
      refine ⟨⟨m2.1, fun h => ?_, ?_⟩, m2.2⟩
      · rw [fb cpub (by omega)]; exact hM.1.2.1 h
      · rw [fb (cpub + 1) (by omega)]; exact hM.1.2.2
    · intro i hi
      rw [hmem, fb _ (by omega)]
      exact hE1 i hi
    · exact hK2
    · rw [Locals.set_other _ _ (by decide)]; exact hdi'
    · rw [Locals.set_other _ _ (by decide)]; exact hbp'

end Locked

end TTop
