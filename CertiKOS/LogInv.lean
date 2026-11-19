import CertiKOS.Layer

/-!
# Invariants along the shared log

Until now `Triple.locked` assumed that the region found under the lock
matches abstract data satisfying the operation's precondition. This file
makes the invariant a property of the **log**, so it is established once and
then carried by every operation.

* `LInv i J l`: the log `l` is valid, and the region last released on lock
  `i` satisfies `J`.
* `RelyJ εR c i J`: the rely. Whatever the environment appends, the region
  last released on lock `i` still satisfies `J`. It is what the other CPUs
  guarantee by `Triple.locked_inv`.
* `rstep_hmem`: an event leaves the last released region alone unless it is a
  release by a holder that has written.
* `acquire_runs_inv`: under the rely, **acquiring finds a region satisfying
  `J`**.
* `Triple.locked_inv`: **`acquire; s; release` carries the invariant.** If
  the log satisfies `∃ d, M d b ∧ I d` on entry, the region found matches
  some `d` with `I`. For any such `d` with the precondition `P`, the call
  finishes, and the log on exit satisfies `∃ d', M d' b ∧ I' d'`, where `I'`
  is what `s` establishes from `I`.
* `relyJ_noEnv`, `relyJ_of_no_release`: the rely holds with no environment,
  and for an environment that does not release the lock.

What is not here: deriving `RelyJ` from the other CPUs' guarantees (the
linking step of `Link.lean`, redone with `J`).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LogInv

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding
  RDI consO lift)
open LockRegionCPU KernFrame Layer

/-- The log is valid and the region last released on lock `i` satisfies `J`. -/
def LInv (i : Nat) (J : Region → Prop) (l : RLog) : Prop :=
  ∃ S H, rreplay l = some (S, H) ∧ J (hmemR i H)

theorem LInv.mono {i : Nat} {J J' : Region → Prop} {l : RLog} (h : LInv i J l) (hJ : ∀ b, J b → J' b) :
    LInv i J' l := by
  obtain ⟨S, H, hl, hj⟩ := h
  exact ⟨S, H, hl, hJ _ hj⟩

/-- **The rely with an invariant.** The environment's events keep `J` on the
region last released on lock `i`. -/
def RelyJ (εR : REnv) (c : CPU) (i : Nat) (J : Region → Prop) : Prop :=
  ∀ l S H S' H', rreplay l = some (S, H) → rreplay (rpull εR c l) = some (S', H') →
    J (hmemR i H) → J (hmemR i H')

/-- Only `incNow` by a holder is a release. -/
theorem pstep_rel {s s' : PState} {e : Event} {d : CPU} (h : pstep s e = some (s', some (.rel d))) :
    ∃ t, s.phase e.cpu = .holding t := by
  obtain ⟨c, k⟩ := e
  simp only [pstep] at h
  split at h
  case isFalse => simp at h
  cases k <;> cases hph : s.phase c <;> simp only [hph] at h <;> try simp at h
  all_goals first
    | exact ⟨_, rfl⟩
    | (split at h <;> simp at h)

/-- **An event changes the last released region only if it is a release by a
holder that has written.** -/
theorem rstep_hmem {S S' : RState} {H : HLogR} {e : REvent} {o : Option HEventR} (hd : RDI S H)
    (hs : rstep S e = some (S', o)) (i : Nat) (hq : Holding S e.cpu i → S.dirty i = false) :
    hmemR i (consO o H) = hmemR i H := by
  obtain ⟨c, j, k⟩ := e
  cases k with
  | pull =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs; rfl
    · simp at hs
  | wr a v =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs; rfl
    · simp at hs
  | tk k =>
    simp only [rstep] at hs
    split at hs
    · simp at hs
    · rename_i p' o' hps
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
      by_cases hji : j = i
      · subst hji
        cases o' with
        | none => rfl
        | some he =>
          cases he with
          | acq d => rfl
          | rel d =>
            obtain ⟨t, ht⟩ := pstep_rel hps
            have hcl := hq ⟨t, ht⟩
            show hmemR j (HEventR.relR d j (S.mem j) :: H) = hmemR j H
            simp only [hmemR, if_true]
            exact (hd j).1 hcl
      · exact LockRegion.hmemR_lift_other hji _ _ _

/-- **Lock-only runs keep the invariant**, the log valid and a fresh holder
clean. -/
theorem lock_run_inv {εR : REnv} {c : CPU} {i : Nat} (hRR : RelyR εR c) {J : Region → Prop}
    (hRJ : RelyJ εR c i J) {x z : Config APrim RLog} (h : Star (rprimsA εR c) x z) :
    LockS x.stmt → LockK x.cont →
    (∃ S H, rreplay x.abs = some (S, H) ∧ Clean c i S ∧ J (hmemR i H)) → AOK (erase z.abs) →
    ∃ S H, rreplay z.abs = some (S, H) ∧ Clean c i S ∧ J (hmemR i H) := by
  induction h with
  | refl => intro _ _ hv _; exact hv
  | @step a b d hs hrest ih =>
    intro hS hK hv hz
    obtain ⟨hS', hK'⟩ := lock_step hS hK hs
    obtain ⟨ys, hys⟩ := lock_star_ext hrest hS' hK'
    have hb : AOK (erase b.abs) := by rw [hys, erase_append] at hz; exact aok_suffix _ hz
    refine ih hS' hK' ?_ hz
    rcases step_abs hs with heq | ⟨t, p, args, v, hst, hp⟩
    · rw [heq]; exact hv
    · rw [hst] at hS
      obtain ⟨e, ea, hl', hec, hea⟩ := lock_call_shape hS hp
      obtain ⟨S, H, hl, hq, hJ⟩ := hv
      obtain ⟨S1, H1, hl1⟩ := hRR _ S H hl
      obtain ⟨g1, g2⟩ := rothers (c := c) (i := i) hl (εR.query c a.abs) (εR.noSelf c a.abs) hl1
      have hq1 : Clean c i S1 := fun hh => by
        have hh0 : LockRegion.Holding S c i := by obtain ⟨t', ht⟩ := hh; exact ⟨t', by rw [← g1 i]; exact ht⟩
        exact (g2 hh0).2 (hq hh0)
      have hJ1 : J (hmemR i H1) := hRJ _ S H S1 H1 hl hl1 hJ
      rw [hl'] at hb ⊢
      have hb' : AOK (ea :: erase (rpull εR c a.abs)) := by
        simpa [erase, List.filterMap_cons, hea] using hb
      obtain ⟨S2, H2, hl2, hq2⟩ := own_lock_event hl1 hq1 hec hea hb'
      obtain ⟨S1', H1', o, hl1', hstep, hH2⟩ := LockRegion.rreplay_cons hl2
      rw [hl1] at hl1'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl1'; obtain ⟨rfl, rfl⟩ := hl1'
      refine ⟨S2, H2, hl2, hq2, ?_⟩
      rw [hH2, rstep_hmem (LockRegion.rreplay_di hl1) hstep i (by rw [hec]; exact hq1)]
      exact hJ1

/-- **Acquire, with the invariant.** The lock is taken, and the region found
satisfies `J`. -/
theorem acquire_runs_inv {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} {J : Region → Prop} (hRJ : RelyJ εR c iv.toNat J)
    (hJ : J (hmemR iv.toNat H)) (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ1 : Locals) (r1 : RLog) (H1 : HLogR), Runs (rprimsA εR c) acquireA σ l σ1 r1 ∧
      CS1 c iv.toNat r1 (hmemR iv.toNat H1) ∧ J (hmemR iv.toNat H1) ∧ σ1 "lk" = iv ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) := by
  obtain ⟨SA, HA, hA, hlkA⟩ := rreplay_erase hl
  have hidleA : (SA.lk iv.toNat).phase c = .idle := by rw [hlkA]; exact hidle
  obtain ⟨r, hspec⟩ := LockArray.acquireA_live_bounded hc hRA hA hidleA bound K hK hF
  obtain ⟨r0, σ1, -, -, hσ1, hstA⟩ := LockArray.acquireA_sim ε c _ σ iv (erase l) r .stop hσ hspec
  obtain ⟨-, -, SA1, HA1, hA1, hholdA, -, -⟩ := LockArray.acquireA_guarantee hc hRA hA hidleA hspec
  obtain ⟨⟨s1, k1, σy, r1⟩, hstR, hy⟩ := star_liftR hE c hstA ⟨acquireA, .stop, σ, l⟩ rfl lockS_acquireA trivial
  simp only [erC, Config.mk.injEq] at hy
  obtain ⟨rfl, rfl, rfl, her⟩ := hy
  obtain ⟨S1, H1, hl1, hq1, hJ1⟩ := lock_run_inv (i := iv.toNat) hRR hRJ hstR lockS_acquireA trivial
    ⟨S, H, hl, (fun hh => by obtain ⟨t, ht⟩ := hh; rw [hidle] at ht; cases ht), hJ⟩
    ⟨SA1, HA1, by rw [her]; exact hA1⟩
  have hold1 : Holding S1 c iv.toNat := by
    obtain ⟨SA1', HA1', hA1', hlk1'⟩ := rreplay_erase hl1
    rw [her, hA1] at hA1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA1'; obtain ⟨rfl, -⟩ := hA1'
    obtain ⟨t, ht⟩ := hholdA; exact ⟨t, by rw [← hlk1']; exact ht⟩
  have hsee : S1.mem iv.toNat = hmemR iv.toNat H1 := LockRegion.acquire_sees hl1 (hq1 hold1)
  have hσlk : σy "lk" = iv := by
    rw [hσ1 "lk" (by decide) (by decide) (by decide) (by decide)]; exact hσ
  exact ⟨σy, r1, H1, Runs.of_stop hstR, ⟨S1, H1, hl1, hold1, hsee⟩, hJ1, hσlk, hσ1⟩

/-- **From a triple to the lock, with the invariant on the log.**
`acquire(lk); s; release(lk)` acquires on any log whose last released region
matches a `d` with `I`. The region it finds matches such a `d`. For any such
`d` with `P`, the call finishes on a valid log, idle, and the region it
releases matches a `d'` with `I'` and `Q`. -/
theorem Triple.locked_inv {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {D : Type} {M : D → Region → Prop} {P : Locals → D → Prop}
    {F : Nat → Prop} {s : Stmt APrim} {Q : Locals → D → Locals → D → Prop}
    (hT : Triple εR c iv.toNat M F P s Q) {I I' : D → Prop}
    (hRJ : RelyJ εR c iv.toNat (fun b => ∃ d, M d b ∧ I d))
    (hJ : ∃ d, M d (hmemR iv.toNat H) ∧ I d)
    (hQI : ∀ σ d σ' d', I d → P σ d → Q σ d σ' d' → I' d') :
    ∃ (σ1 : Locals) (r1 : RLog) (H1 : HLogR), Runs (rprimsA εR c) acquireA σ l σ1 r1 ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) ∧
      (∃ d, M d (hmemR iv.toNat H1) ∧ I d) ∧
      ∀ d, M d (hmemR iv.toNat H1) → I d → P σ1 d →
        ∃ (σ2 : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR) (d' : D),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq s relA), .stop, σ, l⟩ ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          M d' (hmemR iv.toNat H3) ∧ I' d' ∧ Q σ1 d σ2 d' := by
  obtain ⟨σ1, r1, H1, hacq, hcs, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound K hK hF σ hσ
  refine ⟨σ1, r1, H1, hacq, hfr, hJ1, fun d hM hI hP => ?_⟩
  obtain ⟨σ2, l2, b2, d', hrun, hcs2, hM2, hlk2, -, hQ⟩ := hT σ1 r1 _ d (by rw [hlk1]) hcs hM hP
  obtain ⟨rb, S3, H3, hrel, hl3, hid, hmem⟩ := release_runs (εR := εR) hRR hc hcs2 (hlk2.trans hlk1)
  exact ⟨σ2, rb, S3, H3, d', (Runs.seq hacq (Runs.seq hrun hrel)) .stop, hl3, hid, by rw [hmem]; exact hM2,
    hQI _ _ _ _ hI hP hQ, hQ⟩

/-- With no environment the rely holds. -/
theorem relyJ_noEnv (c : CPU) (i : Nat) (J : Region → Prop) : RelyJ LockRegion.noEnvR c i J := by
  intro l S H S' H' hl hl' hJ
  have e : rpull LockRegion.noEnvR c l = l := rfl
  rw [e, hl] at hl'
  simp only [Option.some.injEq, Prod.mk.injEq] at hl'; obtain ⟨-, rfl⟩ := hl'
  exact hJ

/-- Events that are not releases of lock `i` leave its last released region
alone. -/
theorem hmem_no_release {i : Nat} : ∀ (xs : RLog) {l : RLog} {S S' : RState} {H H' : HLogR},
    (∀ e ∈ xs, ¬ (e.lk = i ∧ e.kind = .tk .incNow)) → rreplay l = some (S, H) →
    rreplay (xs ++ l) = some (S', H') → hmemR i H' = hmemR i H
  | [], l, S, S', H, H', _, hl, hl' => by
    simp only [List.nil_append] at hl'; rw [hl] at hl'
    simp only [Option.some.injEq, Prod.mk.injEq] at hl'; obtain ⟨-, rfl⟩ := hl'; rfl
  | e :: xs, l, S, S', H, H', hx, hl, hl' => by
    obtain ⟨S2, H2, o, hl2, hs, rfl⟩ := LockRegion.rreplay_cons hl'
    have ih := hmem_no_release xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2
    rw [← ih]
    have hne := hx e List.mem_cons_self
    obtain ⟨c, j, k⟩ := e
    cases k with
    | pull =>
      simp only [rstep] at hs
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs; rfl
      · simp at hs
    | wr a v =>
      simp only [rstep] at hs
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs; rfl
      · simp at hs
    | tk k =>
      simp only [rstep] at hs
      split at hs
      · simp at hs
      · rename_i p' o' hps
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
        by_cases hji : j = i
        · subst hji
          cases o' with
          | none => rfl
          | some he =>
            cases he with
            | acq d => rfl
            | rel d =>
              exfalso
              simp only [pstep] at hps
              split at hps
              case isFalse => simp at hps
              cases k <;> cases hph : (S2.lk j).phase c <;> simp only [hph] at hps <;> try simp at hps
              all_goals first
                | exact hne ⟨rfl, rfl⟩
                | (split at hps <;> simp at hps)
        · exact LockRegion.hmemR_lift_other hji _ _ _

/-- An environment that never releases lock `i` satisfies the rely. -/
theorem relyJ_of_no_release {εR : REnv} {c : CPU} {i : Nat} (J : Region → Prop)
    (h : ∀ l, ∀ e ∈ εR.query c l, ¬ (e.lk = i ∧ e.kind = .tk .incNow)) : RelyJ εR c i J := by
  intro l S H S' H' hl hl' hJ
  rw [hmem_no_release (εR.query c l) (h l) hl hl']; exact hJ

end LogInv
