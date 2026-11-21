import CertiKOS.THLock

/-!
# The page fault and the yield on the full state, with the lock

`THLock.syscall_h_locked` carries `GoodH` (the full state: the process
layers, the consoles, the VMX blocks, the EPT's upper tables) across a system
call. A page fault and a yield must keep it too, or the invariant on the log
would be lost at the next trap of either kind. `TLock` proves them for the
process state (`Good`); here they are restated for `GoodH`.

* `matchHP_frame`: a process-layer state matched by a region that leaves
  the cells from the user contexts to the pages alone keeps the consoles,
  the VMX blocks and the EPT of the full state.
* `pgf_h_locked`: **a page fault on the full state, with the lock**.
* `yield_h_locked`: **a yield on the full state, with the lock**.

Neither touches the consoles or the VMX state: both run on the process
layers (`pgf_handler_run`, `sys_yield_run`), whose footprints lie below the
user contexts or in the pages.
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
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc FlatMem TTrap
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)
open VVMX (XSt MatchX XF)

open LockArray (AEnv ALog acquireA apull)
open LockRegion (RState HLogR rreplay hmemR)
open LogInv TSysCall TInv TLock

section Locked2
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub elb mc kl kh
  pstart : Nat}
variable {elf : Nat → Nat} {code : Nat → Stmt KPrim} {lk : Val}

local notation "MUP" => MatchUP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub
local notation "MHP" => MatchHP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub
local notation "GH" => GoodH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub
  elb mc kl kh pstart elf code lk
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- **The rest of the full state is kept** by a region that leaves the cells
from the user contexts to the pages alone. -/
theorem matchHP_frame (hL : HL) {d : HData} {u : UData} {b b' : Region} (hM : MHP d b) (hU : MUP u b')
    (hf : ∀ k, ucb + 17 * num_proc ≤ k → k < pb → b' k = b k) : MHP { d with toUData := u } b' := by
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep; have := hL.hup
  exact ⟨hU, matchOut_frame hM.2.1 (fun k hk => hf k (by unfold OF at hk; omega) (by unfold OF at hk; omega)),
    matchX_of (matchX_frame hM.2.2.1 (fun k h1 h2 => hf k (by omega) (by unfold VEPT.NPG at h2; omega))
      hL.hxv hL.hve) rfl rfl rfl,
    VEPT.matchUp_frame hM.2.2.2 (fun a ha => hf a (by unfold VEPT.InUp upb at ha; omega)
      (by unfold VEPT.InUp upb at ha; omega))⟩

/-- **A page fault on the full state, with the lock at the boundary.** -/
theorem pgf_h_locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU)
    (hRA : LockArray.RelyA ε c) (entry : Nat → Nat) (tn : Nat) (hL : HL)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) (hnn : num_proc ≤ num_id)
    (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub)
    (hentry : code (entry tn) = lockedK (mapS .base (pgfEntryS cb cidb maxpage pb fb ucb cpub)))
    {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hidle : (S.lk lk.toNat).phase c = .idle)
    (bound : ALog → Nat) (Kb : Nat) (hK : ∀ l, bound l ≤ Kb)
    (hF : LockArray.FairA ε c lk.toNat (ticket (LockArray.projL lk.toNat (apull ε c (erase l)))) bound)
    {pool : Nat → KCtx} (hRJ : RelyJ εR c lk.toNat (fun b => ∃ d, GH d b ∧ d.kctxt = pool))
    (hJ : ∃ d, GH d (hmemR lk.toNat H) ∧ d.kctxt = pool) (ur0 : Nat → Val) (σ : Locals) (hσ : σ "lk" = lk)
    {vadr : Nat} (hv : vadr < 2 ^ 32) (hva : σ "vaddr" = BitVec.ofNat 32 vadr) :
    ∃ H1 : HLogR, (∃ d, GH d (hmemR lk.toNat H1) ∧ d.kctxt = pool) ∧
      ∀ (d : HData) (d1 d2 d3 : UData) (rs rs' : UContext), GH d (hmemR lk.toNat H1) → d.kctxt = pool →
        (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) →
        proc_exit_user_spec rs d.toUData = some d1 → ptfault_resv_spec maxpage num_proc vadr d1 = some d2 →
        proc_start_user_spec d2 = some (d3, rs') →
        ∃ (ur : Nat → Val) (l' : RLog) (S' : RState) (H' : HLogR),
          UStar εR c code entry lk (.user ur0 pool l) (.user ur pool l') ∧
          rreplay l' = some (S', H') ∧ (S'.lk lk.toNat).phase c = .idle ∧
          GH { d with toUData := d3 } (hmemR lk.toNat H') ∧
          d3.kctxt = pool ∧ ∀ n, n < 17 → ∀ v, rs' n = some v → ur n = v := by
  obtain ⟨σ1, r1, H1, hacq, hcs1, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound Kb hK hF σ hσ
  refine ⟨H1, hJ1, fun d d1 d2 d3 rs rs' hG hpool hrs h1 h2 h3 => ?_⟩
  obtain ⟨hM, hE1, hI, hik, hP⟩ := hG
  have hrs1 : ∀ n, n < 17 → ∀ v, rs n = some v → σ1 (ureg n) = v := fun n hn v hv => by
    obtain ⟨a, b', c', e⟩ := TLock.ureg_ne n hn
    rw [hfr _ a b' c' e]; exact hrs n hn v hv
  have hva1 : σ1 "vaddr" = BitVec.ofNat 32 vadr := by
    rw [hfr "vaddr" (by decide) (by decide) (by decide) (by decide)]; exact hva
  obtain ⟨σ', l', b', hr, hcs', hM', hreg, hfb, hfo⟩ := pgf_handler_run εR c lk.toNat hL.ulay hcp0 hcp1 hmax hnum
    hmp hnn (kl := kl) (kh := kh) hv (σ := σ1) (by rw [hlk1]) hcs1 hM.1 hva1 hI.cid hI.atinv (hI.uq _) hrs1 h1 h2 h3
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
    ⟨by rw [hmem]; exact matchHP_frame hL hM hM' hfo,
      fun i hi => by rw [hmem, hfb _ (by omega) (by omega)]; exact hE1 i hi, I3, hik3, P3⟩,
    hk3, fun n hn v hv => ?_⟩
  · refine .step (.trap ur0 pool l tn σ hσ) ?_
    rw [hentry]
    exact UStar.iret ((kstar_seq hacq _ .stop pool).trans ((KStar.single (kstep_seq _ _ .stop σ1 pool r1)).trans
      ((kstar_base hr relK pool).trans ((KStar.single (kstep_skip_seq _ .stop σ' pool l')).trans
        (kstar_base hrel .stop pool)))))
  · show (σ'.set "_" 0) (ureg n) = v
    rw [Locals.set_other _ _ (TLock.ureg_ne n hn).2.2.1]; exact hreg n hn v hv

/-- **A yield on the full state, with the lock at the boundary.** The caller
is parked holding the lock; the head `la` of the ready queue is resumed and
releases the lock on its way to user mode. -/
theorem yield_h_locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU)
    (hRA : LockArray.RelyA ε c) (entry : Nat → Nat) (tn : Nat) (hL : HL)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub)
    (hentry : code (entry tn) = lockedK (sysYieldK tb qb num_proc num_chan cidb ucb pb cpub))
    (hcode : code pstart = .seq (startK cidb ucb pb cpub) (mapS .base relA))
    {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hidle : (S.lk lk.toNat).phase c = .idle)
    (bound : ALog → Nat) (Kb : Nat) (hK : ∀ l, bound l ≤ Kb)
    (hF : LockArray.FairA ε c lk.toNat (ticket (LockArray.projL lk.toNat (apull ε c (erase l)))) bound)
    {pool : Nat → KCtx} (hRJ : RelyJ εR c lk.toNat (fun b => ∃ d, GH d b ∧ d.kctxt = pool))
    (hJ : ∃ d, GH d (hmemR lk.toNat H) ∧ d.kctxt = pool) (ur0 : Nat → Val) (σ : Locals) (hσ : σ "lk" = lk) :
    ∃ H1 : HLogR, (∃ d, GH d (hmemR lk.toNat H1) ∧ d.kctxt = pool) ∧
      ∀ (d : HData) (d1 : UData) (rs : UContext) (ql : List Nat) (la : Nat), GH d (hmemR lk.toNat H1) →
        d.kctxt = pool → (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) →
        proc_exit_user_spec rs d.toUData = some d1 →
        d.abq num_chan = .AbQValid ql → ql.getLastD num_proc = la → la ≠ num_proc →
        ∃ (ur : Nat → Val) (d3 : UData) (l' : RLog) (S' : RState) (H' : HLogR),
          UStar εR c code entry lk (.user ur0 pool l) (.user ur d3.kctxt l') ∧
          rreplay l' = some (S', H') ∧ (S'.lk lk.toNat).phase c = .idle ∧
          GH { d with toUData := d3 } (hmemR lk.toNat H') ∧
          d3.cid = la ∧ ∀ n, n < 17 → ∀ v, d.uctxt la n = some v → ur n = v := by
  have hU := hL.ulay
  have hCL := hU.ilay.clay
  have := hU.hub0; have := hU.hue; have := hU.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  obtain ⟨σ1, r1, H1, hacq, hcs1, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound Kb hK hF σ hσ
  refine ⟨H1, hJ1, fun d d1 rs ql la hG hpool hrs h1 hq hla hne => ?_⟩
  obtain ⟨hM, hE1, hI, hik, hP⟩ := hG
  have hrs1 : ∀ n, n < 17 → ∀ v, rs n = some v → σ1 (ureg n) = v := fun n hn v hv => by
    obtain ⟨a, b', c', e⟩ := TLock.ureg_ne n hn
    rw [hfr _ a b' c' e]; exact hrs n hn v hv
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  subst hd1
  obtain ⟨σf, l2, b2, hks, c2, m2, hne2, hI2, hlt, hcv2, hlkf, hfb2, hfo2⟩ := sys_yield_run εR c lk.toNat code hU
    hcp0 hcp1 (σ := σ1) (K := relK) (by rw [hlk1]) hcs1 hM.1 hI.cid hI.ainv hI.cur hrs1 h1 hq hla hne
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
  let D1 : UData := { d.toUData with ikern := true, PT := 0, ipt := true, uctxt := setAt d.uctxt d.cid rs }
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
  obtain ⟨σ3, l3, b3, hr3, c3, m3, hreg, f3⟩ := procStartUser_run εR c lk.toNat hU hcp0 hcp1
    (σ := (d.kctxt la).locals) (by rw [hlkB]) c2 m2 ⟨fun _ => hne2, fun _ => hpgY⟩ hlt hs
  have hlk3 : σ3 "lk" = lk := by rw [hr3.frame rfl, hlkB]
  obtain ⟨rb, S4, H4, hrel, hl4, hid4, hmem⟩ := release_runs (εR := εR) hRR hc c3 hlk3
  obtain ⟨I3, hik3⟩ := start_keeps hs hKY
  have P3 := pool_start hs hPY
  refine ⟨regsOf (σ3.set "_" 0), _, rb, S4, H4, ?_, hl4, hid4,
    ⟨by rw [hmem]; exact matchHP_frame hL hM m3 (fun k h1' h2' => by rw [f3 _ (by omega), hfo2 _ h1' h2']),
      fun i hi => by rw [hmem, f3 _ (by omega), hfb2 _ (by omega) (by omega)]; exact hE1 i hi,
      I3, hik3, P3⟩, rfl, fun n hn v hv => ?_⟩
  · refine .step (.trap ur0 pool l tn σ hσ) ?_
    rw [hentry, ← hpool]
    refine UStar.iret ((kstar_seq hacq _ .stop d.kctxt).trans ((KStar.single (kstep_seq _ _ .stop σ1 d.kctxt r1)).trans
      (hks.trans (hks2.trans ((kstar_base hr3 relK Y.kctxt).trans ((KStar.single (kstep_skip_seq _ .stop σ3 Y.kctxt l3)).trans
        (kstar_base hrel .stop Y.kctxt)))))))
  · show (σ3.set "_" 0) (ureg n) = v
    rw [Locals.set_other _ _ (TLock.ureg_ne n hn).2.2.1]
    refine hreg n hn v ?_
    show setAt d.uctxt d.cid rs la n = some v
    rw [setAt_ne _ _ hlc]
    exact hv

end Locked2

end TTop
