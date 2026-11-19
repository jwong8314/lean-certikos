import CertiKOS.KernFrame

/-!
# Layers: verifying code against the specification of the layer below

mCertiKOS verifies each layer's C code against the *specifications* of the
primitives it calls, not against their code. This file gives the ports that.

* `Triple εR c i M F P s Q`: inside a critical section on lock `i`, whenever the
  region matches abstract data `d` (`M d b`) and the precondition `P` holds,
  the code `s` runs to completion, the region again matches some `d'`, and
  `Q` relates before and after. A primitive's triple is its interface: callers
  use the triple and never look at its code.
* A triple also names a footprint `F`: the cells the code may write.
* `Triple.seq`, `Triple.conseq`, `Triple.widen`: sequencing and weakening.
* `Triple.lift`: **frame.** A primitive keeps its interface when the abstract
  state grows, provided what was added survives writes inside the footprint.
* `acquire_runs`, `release_runs`: `KernFrame.cs_guarantee1` in two halves.
* `Triple.locked`: **from a triple to the lock.** `acquire(lk); s; release(lk)`
  first acquires, whatever the region. If the region it then finds matches
  `d` and `P` holds, the whole call finishes on a valid log, and the region
  it releases matches a `d'` related to `d` by `Q`.

Unlike `cs_guarantee1`, the code `s` need not be shown to run on regions that
match nothing. That is what lets a proof assume the invariant.
-/

namespace Layer

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernFrame

/-- **Acquire.** The lock is taken, and the region is the one the previous
holder released. -/
theorem acquire_runs {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ1 : Locals) (r1 : RLog) (H1 : HLogR), Runs (rprimsA εR c) acquireA σ l σ1 r1 ∧
      CS1 c iv.toNat r1 (hmemR iv.toNat H1) ∧ σ1 "lk" = iv ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) := by
  obtain ⟨SA, HA, hA, hlkA⟩ := rreplay_erase hl
  have hidleA : (SA.lk iv.toNat).phase c = .idle := by rw [hlkA]; exact hidle
  obtain ⟨r, hspec⟩ := LockArray.acquireA_live_bounded hc hRA hA hidleA bound K hK hF
  obtain ⟨r0, σ1, -, -, hσ1, hstA⟩ := LockArray.acquireA_sim ε c _ σ iv (erase l) r .stop hσ hspec
  obtain ⟨-, -, SA1, HA1, hA1, hholdA, -, -⟩ := LockArray.acquireA_guarantee hc hRA hA hidleA hspec
  obtain ⟨⟨s1, k1, σy, r1⟩, hstR, hy⟩ := star_liftR hE c hstA ⟨acquireA, .stop, σ, l⟩ rfl lockS_acquireA trivial
  simp only [erC, Config.mk.injEq] at hy
  obtain ⟨rfl, rfl, rfl, her⟩ := hy
  obtain ⟨S1, H1, hl1, hq1⟩ := lock_run_valid (i := iv.toNat) hRR hstR lockS_acquireA trivial
    ⟨S, H, hl, fun hh => by obtain ⟨t, ht⟩ := hh; rw [hidle] at ht; cases ht⟩ ⟨SA1, HA1, by rw [her]; exact hA1⟩
  have hold1 : Holding S1 c iv.toNat := by
    obtain ⟨SA1', HA1', hA1', hlk1'⟩ := rreplay_erase hl1
    rw [her, hA1] at hA1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA1'; obtain ⟨rfl, -⟩ := hA1'
    obtain ⟨t, ht⟩ := hholdA; exact ⟨t, by rw [← hlk1']; exact ht⟩
  have hsee : S1.mem iv.toNat = hmemR iv.toNat H1 := LockRegion.acquire_sees hl1 (hq1 hold1)
  have hσlk : σy "lk" = iv := by
    rw [hσ1 "lk" (by decide) (by decide) (by decide) (by decide)]; exact hσ
  exact ⟨σy, r1, H1, Runs.of_stop hstR, ⟨S1, H1, hl1, hold1, hsee⟩, hσlk, hσ1⟩

/-- **Release.** The log stays valid, we are idle, and the region released is
the one we held. -/
theorem release_runs {εR : REnv} {c : CPU} (hRR : RelyR εR c) (hc : c < NCPU) {iv : Val} {r2 : RLog}
    {b2 : Region} (h : CS1 c iv.toNat r2 b2) {σ2 : Locals} (hσ2 : σ2 "lk" = iv) :
    ∃ (rb : RLog) (S3 : RState) (H3 : HLogR), Runs (rprimsA εR c) relA σ2 r2 (σ2.set "_" 0) rb ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ hmemR iv.toNat H3 = b2 := by
  obtain ⟨S2, H2, hl2, hold2, hb2⟩ := h
  obtain ⟨S2', H2', hl2'⟩ := hRR _ S2 H2 hl2
  obtain ⟨g1, g2⟩ := rothers (c := c) (i := iv.toNat) hl2 (εR.query c r2) (εR.noSelf c r2) hl2'
  obtain ⟨t, ht⟩ := hold2
  have ht' : (S2'.lk iv.toNat).phase c = .holding t := by rw [g1 iv.toNat]; exact ht
  have hps : pstep (S2'.lk iv.toNat) ⟨c, .incNow⟩ = some (⟨(S2'.lk iv.toNat).ticket, (S2'.lk iv.toNat).now + 1,
      setPhase (S2'.lk iv.toNat).phase c .idle⟩, some (.rel c)) := by simp [pstep, hc, ht']
  have hrs : rstep S2' (rev c iv.toNat .incNow) = some (⟨upd S2'.lk iv.toNat ⟨(S2'.lk iv.toNat).ticket,
      (S2'.lk iv.toNat).now + 1, setPhase (S2'.lk iv.toNat).phase c .idle⟩, S2'.mem,
      upd S2'.dirty iv.toNat false⟩, some (.relR c iv.toNat (S2'.mem iv.toNat))) := by
    simp [rstep, rev, hps, LockRegion.lift]
  have hl3 := LockRegion.rreplay_cons_of hl2' hrs
  have hmem2' : S2'.mem iv.toNat = S2.mem iv.toNat := (g2 ⟨t, ht⟩).1
  refine ⟨rev c iv.toNat .incNow :: rpull εR c r2, _, _,
    fun _ => Star.single (by simp [step, rprimsA, relA, Expr.eval, lkE, hσ2]), hl3, by simp, ?_⟩
  simp [LockRegion.consO, hmemR, hmem2', hb2]

/-- **A primitive's interface.** In a critical section on lock `i`, on a region
matching `d` with `P`, the code `s` runs to completion and leaves a region
matching some `d'` with `Q`. -/
def Triple (εR : REnv) (c : CPU) (i : Nat) {D : Type} (M : D → Region → Prop) (F : Nat → Prop)
    (P : Locals → D → Prop) (s : Stmt APrim) (Q : Locals → D → Locals → D → Prop) : Prop :=
  ∀ (σ : Locals) (l : RLog) (b : Region) (d : D), (σ "lk").toNat = i → CS1 c i l b → M d b → P σ d →
    ∃ (σ' : Locals) (l' : RLog) (b' : Region) (d' : D), Runs (rprimsA εR c) s σ l σ' l' ∧ CS1 c i l' b' ∧
      M d' b' ∧ σ' "lk" = σ "lk" ∧ (∀ k, ¬ F k → b' k = b k) ∧ Q σ d σ' d'

section Rules
variable {εR : REnv} {c : CPU} {i : Nat} {D : Type} {M : D → Region → Prop} {F : Nat → Prop}

theorem Triple.conseq {P P' : Locals → D → Prop} {s : Stmt APrim} {Q Q' : Locals → D → Locals → D → Prop}
    (h : Triple εR c i M F P s Q) (hP : ∀ σ d, P' σ d → P σ d)
    (hQ : ∀ σ d σ' d', P' σ d → Q σ d σ' d' → Q' σ d σ' d') : Triple εR c i M F P' s Q' := by
  intro σ l b d hlk hcs hM hp
  obtain ⟨σ', l', b', d', hr, hc', hM', hlk', hf, hq⟩ := h σ l b d hlk hcs hM (hP σ d hp)
  exact ⟨σ', l', b', d', hr, hc', hM', hlk', hf, hQ σ d σ' d' hp hq⟩

/-- A larger footprint is a weaker claim. -/
theorem Triple.widen {F' : Nat → Prop} {P : Locals → D → Prop} {s : Stmt APrim}
    {Q : Locals → D → Locals → D → Prop} (h : Triple εR c i M F P s Q) (hF : ∀ k, F k → F' k) :
    Triple εR c i M F' P s Q := by
  intro σ l b d hlk hcs hM hp
  obtain ⟨σ', l', b', d', hr, hc', hM', hlk', hf, hq⟩ := h σ l b d hlk hcs hM hp
  exact ⟨σ', l', b', d', hr, hc', hM', hlk', fun k hk => hf k (fun h => hk (hF k h)), hq⟩

/-- Sequencing: the first postcondition gives the second precondition. -/
theorem Triple.seq {P1 P2 : Locals → D → Prop} {s1 s2 : Stmt APrim} {Q1 Q2 : Locals → D → Locals → D → Prop}
    (h1 : Triple εR c i M F P1 s1 Q1) (h2 : Triple εR c i M F P2 s2 Q2)
    (hmid : ∀ σ d σ1 d1, P1 σ d → Q1 σ d σ1 d1 → P2 σ1 d1) :
    Triple εR c i M F P1 (.seq s1 s2) (fun σ d σ' d' => ∃ σ1 d1, Q1 σ d σ1 d1 ∧ Q2 σ1 d1 σ' d') := by
  intro σ l b d hlk hcs hM hp
  obtain ⟨σ1, l1, b1, d1, hr1, hc1, hM1, hlk1, hf1, hq1⟩ := h1 σ l b d hlk hcs hM hp
  obtain ⟨σ2, l2, b2, d2, hr2, hc2, hM2, hlk2, hf2, hq2⟩ :=
    h2 σ1 l1 b1 d1 (by rw [hlk1]; exact hlk) hc1 hM1 (hmid σ d σ1 d1 hp hq1)
  exact ⟨σ2, l2, b2, d2, Runs.seq hr1 hr2, hc2, hM2, hlk2.trans hlk1,
    fun k hk => (hf2 k hk).trans (hf1 k hk), σ1, d1, hq1, hq2⟩

/-- The same relation, stated another way. -/
theorem Triple.iffM {M' : D → Region → Prop} {P : Locals → D → Prop} {s : Stmt APrim}
    {Q : Locals → D → Locals → D → Prop} (h : Triple εR c i M F P s Q) (hM : ∀ d b, M' d b ↔ M d b) :
    Triple εR c i M' F P s Q := by
  intro σ l b d hlk hcs hm hp
  obtain ⟨σ', l', b', d', hr, hc', hM', hlk', hf, hq⟩ := h σ l b d hlk hcs ((hM d b).1 hm) hp
  exact ⟨σ', l', b', d', hr, hc', (hM d' b').2 hM', hlk', hf, hq⟩

/-- An assignment in front of a primitive: the primitive sees the updated locals. -/
theorem Triple.assign_pre {P : Locals → D → Prop} {s : Stmt APrim} {Q : Locals → D → Locals → D → Prop}
    (h : Triple εR c i M F P s Q) (x : Ident) (hx : x ≠ "lk") (e : Expr) :
    Triple εR c i M F (fun σ d => P (σ.set x (e.eval σ)) d) (.seq (.assign x e) s)
      (fun σ d σ' d' => Q (σ.set x (e.eval σ)) d σ' d') := by
  intro σ l b d hlk hcs hM hp
  obtain ⟨σ', l', b', d', hr, hc', hM', hlk', hf, hq⟩ :=
    h (σ.set x (e.eval σ)) l b d (by rw [Locals.set_other _ _ (Ne.symm hx)]; exact hlk) hcs hM hp
  exact ⟨σ', l', b', d', Runs.seq (Runs.assign x e) hr, hc', hM',
    by rw [hlk', Locals.set_other _ _ (Ne.symm hx)], hf, hq⟩

/-- **Frame: a primitive in a larger state.** `D'` extends `D`: `π` projects,
`put` writes back. `M2` is what the larger state adds. If `M2` survives every
change of the region inside the footprint `F` that the primitive's
postcondition allows, the primitive has the same interface in the larger
state. This is how a layer reuses the primitives below it. -/
theorem Triple.lift {D' : Type} {π : D' → D} {put : D' → D → D'} {M2 : D' → Region → Prop}
    {P : Locals → D → Prop} {s : Stmt APrim} {Q : Locals → D → Locals → D → Prop}
    (h : Triple εR c i M F P s Q) (hput : ∀ d' d1, π (put d' d1) = d1)
    (hM2 : ∀ d' b σ σ' d1 b', M2 d' b → M (π d') b → P σ (π d') → Q σ (π d') σ' d1 →
      (∀ k, ¬ F k → b' k = b k) → M2 (put d' d1) b') :
    Triple εR c i (fun d' b => M (π d') b ∧ M2 d' b) F (fun σ d' => P σ (π d')) s
      (fun σ d' σ' d'' => ∃ d1, d'' = put d' d1 ∧ Q σ (π d') σ' d1) := by
  intro σ l b d' hlk hcs ⟨hM, h2⟩ hp
  obtain ⟨σ', l', b', d1, hr, hc', hM', hlk', hf, hq⟩ := h σ l b (π d') hlk hcs hM hp
  exact ⟨σ', l', b', put d' d1, hr, hc', ⟨by rw [hput]; exact hM', hM2 d' b σ σ' d1 b' h2 hM hp hq hf⟩,
    hlk', hf, d1, rfl, hq⟩

end Rules

/-- **From a triple to the lock.** `acquire(lk); s; release(lk)` acquires on
any log. If the region it finds matches `d` with `P`, the call finishes on a
valid log, idle, and the region it releases matches a `d'` with `Q`. -/
theorem Triple.locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {D : Type} {M : D → Region → Prop} {P : Locals → D → Prop}
    {F : Nat → Prop} {s : Stmt APrim} {Q : Locals → D → Locals → D → Prop}
    (hT : Triple εR c iv.toNat M F P s Q) :
    ∃ (σ1 : Locals) (r1 : RLog) (H1 : HLogR), Runs (rprimsA εR c) acquireA σ l σ1 r1 ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) ∧
      ∀ d, M d (hmemR iv.toNat H1) → P σ1 d →
        ∃ (σ2 : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR) (d' : D),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq s relA), .stop, σ, l⟩ ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          M d' (hmemR iv.toNat H3) ∧ Q σ1 d σ2 d' := by
  obtain ⟨σ1, r1, H1, hacq, hcs, hlk1, hfr⟩ :=
    acquire_runs hE hRR hc hRA hl hidle bound K hK hF σ hσ
  refine ⟨σ1, r1, H1, hacq, hfr, fun d hM hP => ?_⟩
  obtain ⟨σ2, l2, b2, d', hrun, hcs2, hM2, hlk2, -, hQ⟩ := hT σ1 r1 _ d (by rw [hlk1]) hcs hM hP
  obtain ⟨rb, S3, H3, hrel, hl3, hid, hmem⟩ := release_runs (εR := εR) hRR hc hcs2 (hlk2.trans hlk1)
  exact ⟨σ2, rb, S3, H3, d', (Runs.seq hacq (Runs.seq hrun hrel)) .stop, hl3, hid, by rw [hmem]; exact hM2, hQ⟩

end Layer
