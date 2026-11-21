import CertiKOS.TInv
import CertiKOS.LogInv

/-!
# The lock at the kernel boundary, and the invariant from one trap to the next

Until now every theorem about the kernel's entry points was inside a critical
section: the lock was held at the trap and still held at the return. Here the
entry points take the lock themselves:

```
locked entry:   acquire(lk); entry; release(lk)
```

and the invariant lives on the shared log (`LogInv`): whenever the lock is
free, the region last released matches a state `d` with `Good d`.

* `lockedK`: an entry point with the lock around it.
* `Good`: what holds of the state each time the lock is released on the way
  back to user mode: the region matches it (`MatchUP`, and the ELF table),
  the kernel invariant `KInv` holds, the processor is in user mode, and every
  ready thread can be resumed (`PoolInv`).
* `PoolInv`: every kernel context has the lock in its local `lk`, and every
  ready thread other than the running one is either parked by a yield (about
  to run `proc_start_user` and release the lock) or new (about to run
  `code pstart`, which is `proc_start_user; release`).
* `pool_dispatch`, `pool_pgf`: the passages keep `PoolInv`.
* `syscall_locked`: **a system call from user mode, with the lock.** On a log
  whose last released region is `Good` (and whose other CPUs keep it so,
  `RelyJ`), the trap acquires the lock and finds a `Good` state; from any such
  state for which the specifications are defined, the machine goes back to
  user mode, the lock released and idle, the last released region `Good` for
  the state the specifications give.
* `pgf_locked`: **a page fault**, likewise.
* `yield_locked`: **a yield.** The caller is parked holding the lock; the
  head of the ready queue, parked by an earlier yield or new, is resumed and
  releases the lock on its way to user mode (`resume_start`).

What is assumed at each trap is what `Triple.locked_inv` assumes: the rely
on the other CPUs (`RelyJ`, with the invariant) and the fairness of the
lock. The machine still has one copy of the per-CPU state.

So the invariant is carried from one trap to the next, and each trap is
bracketed by the lock.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TLock

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region hmemR setCell)
open LockRegionCPU KernFrame Layer LogInv
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc FlatMem TTrap TSysCall TInv

/-- **An entry point with the lock**: `acquire(lk); s; release(lk)`. -/
def lockedK (s : Stmt KPrim) : Stmt KPrim := .seq (mapS .base acquireA) (.seq s (mapS .base relA))

/-- `proc_start_user`, as kernel code. -/
def startK (cidb ucb pb cpub : Nat) : Stmt KPrim := mapS .base (procStartUserS cidb ucb pb cpub)

/-- What is left after the entry point: the release. -/
def relK : Cont KPrim := .seq (mapS .base relA) .stop

/-- How a ready thread is resumed. -/
def Resumable (code : Nat → Stmt KPrim) (pstart cidb ucb pb cpub : Nat) (k : KCtx) : Prop :=
  (k.stmt = .skip ∧ k.cont = .seq (startK cidb ucb pb cpub) relK) ∨ (k.stmt = code pstart ∧ k.cont = .stop)

/-- **Every ready thread can be resumed.** -/
def PoolInv (code : Nat → Stmt KPrim) (pstart cidb ucb pb cpub num_proc num_chan : Nat) (lk : Val) (d : UData) :
    Prop :=
  ∀ t, t < num_proc → (d.kctxt t).locals "lk" = lk ∧
    (t ≠ d.cid → ∀ s (q : Int), d.abtcb t = .AbTCBValid s q → q ≠ -1 →
      Resumable code pstart cidb ucb pb cpub (d.kctxt t))

theorem ureg_ne : ∀ n, n < 17 → ureg n ≠ "t" ∧ ureg n ≠ "n" ∧ ureg n ≠ "_" ∧ ureg n ≠ "v" := by decide

section
variable {code : Nat → Stmt KPrim} {pstart cidb ucb pb cpub num_proc num_chan : Nat} {lk : Val}

local notation "PI" => PoolInv code pstart cidb ucb pb cpub num_proc num_chan lk

theorem PoolInv.congr {d d' : UData} (h : PI d) (e1 : d'.kctxt = d.kctxt) (e2 : d'.abtcb = d.abtcb)
    (e3 : d'.cid = d.cid) : PI d' := by
  intro t ht
  rw [e1, e2, e3]
  exact h t ht

theorem pool_exit {rs : UContext} {d d1 : UData} (h : proc_exit_user_spec rs d = some d1) (hP : PI d) : PI d1 := by
  obtain ⟨e, -⟩ := exit_shape h; subst e; exact hP.congr rfl rfl rfl

theorem pool_start {d d' : UData} {rs : UContext} (h : proc_start_user_spec d = some (d', rs)) (hP : PI d) : PI d' := by
  obtain ⟨e, -, -⟩ := start_shape h; subst e; exact hP.congr rfl rfl rfl

theorem pool_setReg {reg n : Nat} {d d' : UData} (h : uctx_set_reg_spec reg n d = some d') (hP : PI d) : PI d' := by
  obtain ⟨U, e⟩ := set_reg_shape h; subst e; exact hP.congr rfl rfl rfl

/-- **`proc_create`'s child is ready, and new.** -/
theorem pool_create {num_id mc : Nat} {uentry q : Nat} {d d' : UData} {i : Nat}
    (hnn : num_id ≤ num_proc) (hs : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', i))
    (hP : PI d) : PI d' := by
  unfold proc_create_spec at hs
  simp only at hs
  split at hs
  · rename_i hc
    have hlt := hc.2.2.2.2.1
    cases hq : d.abq num_chan with
    | AbQUndef => rw [hq] at hs; cases hs
    | AbQValid l =>
      rw [hq] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      intro t ht
      dsimp only
      by_cases e : t = d.cid * mc + 1 + (d.AC d.cid).cchildren.length
      · rw [e, setAt_eq, setAt_eq]
        exact ⟨(hP _ (by omega)).1, fun _ _ _ _ _ => Or.inr ⟨rfl, rfl⟩⟩
      · rw [setAt_ne _ _ e, setAt_ne _ _ e]
        exact hP t ht
  · cases hs

/-- **The dispatcher keeps `PoolInv`.** -/
theorem pool_dispatch {num_id mc : Nat} (hnn : num_id ≤ num_proc) {elf : Nat → Nat} {d d' : UData}
    (hs : sys_dispatch_c_spec num_id mc num_chan code pstart elf d = some d') (hP : PI d) : PI d' := by
  unfold sys_dispatch_c_spec at hs
  cases e1 : uctx_arg1_spec d with
  | none => rw [e1] at hs; cases hs
  | some a =>
    rw [e1] at hs; simp only at hs
    by_cases h2 : a = 2
    · rw [if_pos h2] at hs
      unfold trap_proc_create_spec at hs
      repeat' split at hs
      all_goals first
        | exact pool_setReg hs hP
        | exact pool_setReg hs (pool_setReg ‹uctx_set_retval1_spec _ _ = some _›
            (pool_create hnn ‹proc_create_spec _ _ _ _ _ _ _ _ = some _› hP))
        | cases hs
    · rw [if_neg h2] at hs
      by_cases h26 : a = 26
      · rw [if_pos h26] at hs
        obtain ⟨U, e⟩ := get_quota_shape hs
        subst e
        exact hP.congr rfl rfl rfl
      · rw [if_neg h26] at hs
        exact pool_setReg hs hP

theorem pool_pgf {maxpage vadr : Nat} {d d' : UData} (hs : ptfault_resv_spec maxpage num_proc vadr d = some d')
    (hP : PI d) : PI d' := by
  unfold ptfault_resv_spec at hs
  repeat' split at hs
  all_goals first
    | (simp only [Option.some.injEq] at hs; subst hs; exact hP.congr rfl rfl rfl)
    | cases hs

end

theorem pgf_kctxt {maxpage num_proc vadr : Nat} {d d' : UData} (hs : ptfault_resv_spec maxpage num_proc vadr d = some d') :
    d'.kctxt = d.kctxt := by
  unfold ptfault_resv_spec at hs
  repeat' split at hs
  all_goals first
    | (simp only [Option.some.injEq] at hs; subst hs; rfl)
    | cases hs

/-! ## The entry points with the lock -/

section Machine
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb elb cpub mc kl kh pstart : Nat}
variable {elf : Nat → Nat} {code : Nat → Stmt KPrim} {lk : Val}

/-- **What holds each time the lock is released on the way to user mode.** -/
def Good (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub elb mc kl kh pstart : Nat)
    (elf : Nat → Nat) (code : Nat → Stmt KPrim) (lk : Val) (d : UData) (b : Region) : Prop :=
  MatchUP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub d b ∧
    MatchELF num_id elb elf b ∧ KInv num_id mc num_proc num_chan maxpage kl kh d ∧ d.ikern = false ∧
    PoolInv code pstart cidb ucb pb cpub num_proc num_chan lk d

local notation "G" => Good maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub elb mc kl kh
  pstart elf code lk

/-- **A system call, with the lock at the boundary.** -/
theorem syscall_locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU)
    (hRA : LockArray.RelyA ε c) (entry : Nat → Nat) (tn : Nat)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hnum : cb + 5 * num_id < 2 ^ 32)
    (hnn : num_id ≤ num_proc) (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub)
    (hov : num_id * mc + mc + 1 < 2 ^ 32) (hps : pstart < 2 ^ 32)
    (hentry : code (entry tn) = lockedK (sysEntryK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart pb cpub))
    {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hidle : (S.lk lk.toNat).phase c = .idle)
    (bound : ALog → Nat) (Kb : Nat) (hK : ∀ l, bound l ≤ Kb)
    (hF : LockArray.FairA ε c lk.toNat (ticket (LockArray.projL lk.toNat (apull ε c (erase l)))) bound)
    {pool : Nat → KCtx} (hRJ : RelyJ εR c lk.toNat (fun b => ∃ d, G d b ∧ d.kctxt = pool))
    (hJ : ∃ d, G d (hmemR lk.toNat H) ∧ d.kctxt = pool) (ur0 : Nat → Val) (σ : Locals) (hσ : σ "lk" = lk) :
    ∃ H1 : HLogR, (∃ d, G d (hmemR lk.toNat H1) ∧ d.kctxt = pool) ∧
      ∀ (d d1 d2 d3 : UData) (rs rs' : UContext), G d (hmemR lk.toNat H1) → d.kctxt = pool →
        (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) →
        proc_exit_user_spec rs d = some d1 → sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d2 →
        proc_start_user_spec d2 = some (d3, rs') →
        ∃ (ur : Nat → Val) (l' : RLog) (S' : RState) (H' : HLogR),
          UStar εR c code entry lk (.user ur0 pool l) (.user ur d3.kctxt l') ∧
          rreplay l' = some (S', H') ∧ (S'.lk lk.toNat).phase c = .idle ∧ G d3 (hmemR lk.toNat H') ∧
          ∀ n, n < 17 → ∀ v, rs' n = some v → ur n = v := by
  obtain ⟨σ1, r1, H1, hacq, hcs1, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound Kb hK hF σ hσ
  refine ⟨H1, hJ1, fun d d1 d2 d3 rs rs' hG hpool hrs h1 h2 h3 => ?_⟩
  obtain ⟨hM, hE1, hI, hik, hP⟩ := hG
  have hrs1 : ∀ n, n < 17 → ∀ v, rs n = some v → σ1 (ureg n) = v := fun n hn v hv => by
    obtain ⟨a, b', c', e⟩ := ureg_ne n hn
    rw [hfr _ a b' c' e]; exact hrs n hn v hv
  obtain ⟨σ', l', b', hks, hcs', hM', hE', hreg, hlk'⟩ := syscall_dispatch_run εR c lk.toNat code hL hcp0 hcp1
    hnum hnn hel0 hec hov hps (σ := σ1) (K := relK) (by rw [hlk1]) hcs1 hM hE1 hI.cid hI.ainv hI.cv hI.cur.1
    hrs1 h1 h2 h3
  obtain ⟨rb, S3, H3, hrel, hl3, hid3, hmem⟩ := release_runs (εR := εR) hRR hc hcs' (hlk'.trans hlk1)
  obtain ⟨I3, hik3⟩ := start_keeps h3 (dispatch_keeps hnn h2 (exit_keeps h1 hI))
  have P3 := pool_start h3 (pool_dispatch hnn h2 (pool_exit h1 hP))
  refine ⟨regsOf (σ'.set "_" 0), rb, S3, H3, ?_, hl3, hid3,
    ⟨by rw [hmem]; exact hM', by rw [hmem]; exact hE', I3, hik3, P3⟩, fun n hn v hv => ?_⟩
  · refine .step (.trap ur0 pool l tn σ hσ) ?_
    rw [hentry, ← hpool]
    exact UStar.iret ((kstar_seq hacq _ .stop d.kctxt).trans ((KStar.single (kstep_seq _ _ .stop σ1 d.kctxt r1)).trans
      (hks.trans ((KStar.single (kstep_skip_seq _ .stop σ' d3.kctxt l')).trans (kstar_base hrel .stop d3.kctxt)))))
  · show (σ'.set "_" 0) (ureg n) = v
    rw [Locals.set_other _ _ (ureg_ne n hn).2.2.1]; exact hreg n hn v hv

/-- **A page fault, with the lock at the boundary.** The fault address is in
the local `vaddr` at the trap. -/
theorem pgf_locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU)
    (hRA : LockArray.RelyA ε c) (entry : Nat → Nat) (tn : Nat)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) (hnn : num_proc ≤ num_id)
    (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub)
    (hentry : code (entry tn) = lockedK (mapS .base (pgfEntryS cb cidb maxpage pb fb ucb cpub)))
    {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hidle : (S.lk lk.toNat).phase c = .idle)
    (bound : ALog → Nat) (Kb : Nat) (hK : ∀ l, bound l ≤ Kb)
    (hF : LockArray.FairA ε c lk.toNat (ticket (LockArray.projL lk.toNat (apull ε c (erase l)))) bound)
    {pool : Nat → KCtx} (hRJ : RelyJ εR c lk.toNat (fun b => ∃ d, G d b ∧ d.kctxt = pool))
    (hJ : ∃ d, G d (hmemR lk.toNat H) ∧ d.kctxt = pool) (ur0 : Nat → Val) (σ : Locals) (hσ : σ "lk" = lk)
    {vadr : Nat} (hv : vadr < 2 ^ 32) (hva : σ "vaddr" = BitVec.ofNat 32 vadr) :
    ∃ H1 : HLogR, (∃ d, G d (hmemR lk.toNat H1) ∧ d.kctxt = pool) ∧
      ∀ (d d1 d2 d3 : UData) (rs rs' : UContext), G d (hmemR lk.toNat H1) → d.kctxt = pool →
        (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) →
        proc_exit_user_spec rs d = some d1 → ptfault_resv_spec maxpage num_proc vadr d1 = some d2 →
        proc_start_user_spec d2 = some (d3, rs') →
        ∃ (ur : Nat → Val) (l' : RLog) (S' : RState) (H' : HLogR),
          UStar εR c code entry lk (.user ur0 pool l) (.user ur pool l') ∧
          rreplay l' = some (S', H') ∧ (S'.lk lk.toNat).phase c = .idle ∧ G d3 (hmemR lk.toNat H') ∧
          d3.kctxt = pool ∧ ∀ n, n < 17 → ∀ v, rs' n = some v → ur n = v := by
  obtain ⟨σ1, r1, H1, hacq, hcs1, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound Kb hK hF σ hσ
  refine ⟨H1, hJ1, fun d d1 d2 d3 rs rs' hG hpool hrs h1 h2 h3 => ?_⟩
  obtain ⟨hM, hE1, hI, hik, hP⟩ := hG
  have hrs1 : ∀ n, n < 17 → ∀ v, rs n = some v → σ1 (ureg n) = v := fun n hn v hv => by
    obtain ⟨a, b', c', e⟩ := ureg_ne n hn
    rw [hfr _ a b' c' e]; exact hrs n hn v hv
  have hva1 : σ1 "vaddr" = BitVec.ofNat 32 vadr := by
    rw [hfr "vaddr" (by decide) (by decide) (by decide) (by decide)]; exact hva
  obtain ⟨σ', l', b', hr, hcs', hM', hreg, hfb, -⟩ := pgf_handler_run εR c lk.toNat hL hcp0 hcp1 hmax hnum hmp hnn
    (kl := kl) (kh := kh) hv (σ := σ1) (by rw [hlk1]) hcs1 hM hva1 hI.cid hI.atinv (hI.uq _) hrs1 h1 h2 h3
  have hlk' : σ' "lk" = lk := by rw [hr.frame rfl, hlk1]
  obtain ⟨rb, S3, H3, hrel, hl3, hid3, hmem⟩ := release_runs (εR := εR) hRR hc hcs' hlk'
  have I1 := exit_keeps h1 hI
  obtain ⟨I3, hik3⟩ := start_keeps h3 (pgf_keeps h2 I1)
  have P3 := pool_start h3 (pool_pgf h2 (pool_exit h1 hP))
  have hk3 : d3.kctxt = pool := by
    obtain ⟨e3, -, -⟩ := start_shape h3
    obtain ⟨e1, -⟩ := exit_shape h1
    rw [e3, pgf_kctxt h2, e1]; exact hpool
  refine ⟨regsOf (σ'.set "_" 0), rb, S3, H3, ?_, hl3, hid3,
    ⟨by rw [hmem]; exact hM', fun i hi => by rw [hmem, hfb _ (by omega) (by omega)]; exact hE1 i hi, I3, hik3, P3⟩,
    hk3, fun n hn v hv => ?_⟩
  · refine .step (.trap ur0 pool l tn σ hσ) ?_
    rw [hentry]
    exact UStar.iret ((kstar_seq hacq _ .stop pool).trans ((KStar.single (kstep_seq _ _ .stop σ1 pool r1)).trans
      ((kstar_base hr relK pool).trans ((KStar.single (kstep_skip_seq _ .stop σ' pool l')).trans
        (kstar_base hrel .stop pool)))))
  · show (σ'.set "_" 0) (ureg n) = v
    rw [Locals.set_other _ _ (ureg_ne n hn).2.2.1]; exact hreg n hn v hv

/-- **A ready thread, resumed, reaches `proc_start_user` with the release
after it.** -/
theorem resume_start {εR : REnv} {c : CPU} {cidb ucb pb cpub : Nat}
    (hcode : code pstart = .seq (startK cidb ucb pb cpub) (mapS .base relA)) {k : KCtx}
    (hk : Resumable code pstart cidb ucb pb cpub k) (pool : Nat → KCtx) (l : RLog) :
    KStar εR c code ⟨k, pool, l⟩ ⟨⟨startK cidb ucb pb cpub, relK, k.locals⟩, pool, l⟩ := by
  obtain ⟨st, K, σ⟩ := k
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2; subst h1; subst h2
    exact KStar.single (kstep_skip_seq _ _ σ pool l)
  · simp only at h1 h2; subst h2; rw [h1, hcode]
    exact KStar.single (kstep_seq _ _ .stop σ pool l)

/-- **A yield, with the lock at the boundary.** The caller is parked holding
the lock; the head `la` of the ready queue is resumed (parked by an earlier
yield, or new) and releases the lock on its way to user mode. -/
theorem yield_locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU)
    (hRA : LockArray.RelyA ε c) (entry : Nat → Nat) (tn : Nat)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub)
    (hentry : code (entry tn) = lockedK (sysYieldK tb qb num_proc num_chan cidb ucb pb cpub))
    (hcode : code pstart = .seq (startK cidb ucb pb cpub) (mapS .base relA))
    {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hidle : (S.lk lk.toNat).phase c = .idle)
    (bound : ALog → Nat) (Kb : Nat) (hK : ∀ l, bound l ≤ Kb)
    (hF : LockArray.FairA ε c lk.toNat (ticket (LockArray.projL lk.toNat (apull ε c (erase l)))) bound)
    {pool : Nat → KCtx} (hRJ : RelyJ εR c lk.toNat (fun b => ∃ d, G d b ∧ d.kctxt = pool))
    (hJ : ∃ d, G d (hmemR lk.toNat H) ∧ d.kctxt = pool) (ur0 : Nat → Val) (σ : Locals) (hσ : σ "lk" = lk) :
    ∃ H1 : HLogR, (∃ d, G d (hmemR lk.toNat H1) ∧ d.kctxt = pool) ∧
      ∀ (d d1 : UData) (rs : UContext) (ql : List Nat) (la : Nat), G d (hmemR lk.toNat H1) → d.kctxt = pool →
        (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) → proc_exit_user_spec rs d = some d1 →
        d.abq num_chan = .AbQValid ql → ql.getLastD num_proc = la → la ≠ num_proc →
        ∃ (ur : Nat → Val) (d3 : UData) (l' : RLog) (S' : RState) (H' : HLogR),
          UStar εR c code entry lk (.user ur0 pool l) (.user ur d3.kctxt l') ∧
          rreplay l' = some (S', H') ∧ (S'.lk lk.toNat).phase c = .idle ∧ G d3 (hmemR lk.toNat H') ∧
          d3.cid = la ∧ ∀ n, n < 17 → ∀ v, d.uctxt la n = some v → ur n = v := by
  obtain ⟨σ1, r1, H1, hacq, hcs1, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound Kb hK hF σ hσ
  refine ⟨H1, hJ1, fun d d1 rs ql la hG hpool hrs h1 hq hla hne => ?_⟩
  obtain ⟨hM, hE1, hI, hik, hP⟩ := hG
  have hrs1 : ∀ n, n < 17 → ∀ v, rs n = some v → σ1 (ureg n) = v := fun n hn v hv => by
    obtain ⟨a, b', c', e⟩ := ureg_ne n hn
    rw [hfr _ a b' c' e]; exact hrs n hn v hv
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  subst hd1
  obtain ⟨σf, l2, b2, hks, c2, m2, hne2, hI2, hlt, hcv2, hlkf, hfb2, -⟩ := sys_yield_run εR c lk.toNat code hL hcp0
    hcp1 (σ := σ1) (K := relK) (by rw [hlk1]) hcs1 hM hI.cid hI.ainv hI.cur hrs1 h1 hq hla hne
  -- the process resumed is not the caller, and it is on the ready queue
  obtain ⟨s, hai⟩ := hI.ainv.inq la num_chan ql hlt (Nat.le_refl _) hq (last_mem hla hne)
  have hlc : la ≠ d.cid := by
    intro e
    have h := hI.cur.2
    rw [← e, hai] at h
    injection h with e1 e2
    omega
  obtain ⟨hlkB, hres⟩ := hP la hlt
  have hR := hres hlc s _ hai (by omega)
  -- the state after the switch
  let rsK : KCtx := ⟨.skip, .seq (startK cidb ucb pb cpub) relK, σf.set "_" 0⟩
  let D1 : UData := { d with ikern := true, PT := 0, ipt := true, uctxt := setAt d.uctxt d.cid rs }
  let Y := yieldOut num_chan la ql rsK (toK D1)
  have hpgY : (putK D1 Y).pg = true := hpg
  have hs : proc_start_user_spec (putK D1 Y) =
      some ({ putK D1 Y with ikern := false, ipt := false, PT := la }, (setAt d.uctxt d.cid rs) la) := by
    unfold proc_start_user_spec
    exact if_pos ⟨rfl, hpgY, hI.ihost, rfl, hI.init⟩
  have hKY : KInv num_id mc num_proc num_chan maxpage kl kh (putK D1 Y) := by
    exact ⟨hlt, hcv2, hI2, hI.cv, hI.atinv, hI.uq, hpg, hI.ihost, hI.init⟩
  have hPY : PoolInv code pstart cidb ucb pb cpub num_proc num_chan lk (putK D1 Y) := by
    intro t ht
    show (setAt d.kctxt d.cid rsK t).locals "lk" = lk ∧
      (t ≠ la → ∀ s' (q' : Int), setAt (setAt d.abtcb d.cid _) la _ t = .AbTCBValid s' q' → q' ≠ -1 →
        Resumable code pstart cidb ucb pb cpub
        (setAt d.kctxt d.cid rsK t))
    by_cases e : t = d.cid
    · subst e
      rw [setAt_eq]
      refine ⟨?_, fun _ _ _ _ _ => Or.inl ⟨rfl, rfl⟩⟩
      show (σf.set "_" 0) "lk" = lk
      rw [Locals.set_other _ _ (by decide), hlkf, hlk1]
    · rw [setAt_ne _ _ e]
      refine ⟨(hP t ht).1, fun hne' s' q' hs' hq' => ?_⟩
      rw [setAt_ne _ _ hne', setAt_ne _ _ e] at hs'
      exact (hP t ht).2 e s' q' hs' hq'
  -- the resumed thread: `proc_start_user`, then the release
  have hks2 := resume_start (εR := εR) (c := c) hcode hR Y.kctxt l2
  obtain ⟨σ3, l3, b3, hr3, c3, m3, hreg, f3⟩ := procStartUser_run εR c lk.toNat hL hcp0 hcp1
    (σ := (d.kctxt la).locals) (by rw [hlkB]) c2 m2 ⟨fun _ => hne2, fun _ => hpgY⟩ hlt hs
  have hlk3 : σ3 "lk" = lk := by rw [hr3.frame rfl, hlkB]
  obtain ⟨rb, S4, H4, hrel, hl4, hid4, hmem⟩ := release_runs (εR := εR) hRR hc c3 hlk3
  obtain ⟨I3, hik3⟩ := start_keeps hs hKY
  have P3 := pool_start hs hPY
  refine ⟨regsOf (σ3.set "_" 0), _, rb, S4, H4, ?_, hl4, hid4,
    ⟨by rw [hmem]; exact m3, fun i hi => by rw [hmem, f3 _ (by omega), hfb2 _ (by omega) (by omega)]; exact hE1 i hi,
      I3, hik3, P3⟩, rfl, fun n hn v hv => ?_⟩
  · refine .step (.trap ur0 pool l tn σ hσ) ?_
    rw [hentry, ← hpool]
    refine UStar.iret ((kstar_seq hacq _ .stop d.kctxt).trans ((KStar.single (kstep_seq _ _ .stop σ1 d.kctxt r1)).trans
      (hks.trans (hks2.trans ((kstar_base hr3 relK Y.kctxt).trans ((KStar.single (kstep_skip_seq _ .stop σ3 Y.kctxt l3)).trans
        (kstar_base hrel .stop Y.kctxt)))))))
  · show (σ3.set "_" 0) (ureg n) = v
    rw [Locals.set_other _ _ (ureg_ne n hn).2.2.1]
    refine hreg n hn v ?_
    show setAt d.uctxt d.cid rs la n = some v
    rw [setAt_ne _ _ hlc]
    exact hv

end Machine

end TLock
