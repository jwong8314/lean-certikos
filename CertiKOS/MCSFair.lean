import CertiKOS.MCSLock

/-!
# A concrete fair scheduler for the MCS lock: `RelyM`, `FairB`, `FairN` are satisfiable

The MCS analogue of `FairEnv.lean`. Whenever CPU `c` looks at the shared log,
`fairEnvM` acts as follows.

* **`c` holds the lock but has no successor yet.** A successor links. If a
  CPU is already queued behind `c`, it is that one. Otherwise another CPU
  swaps in and links (with only `c` queued, every other CPU is idle).
* **Otherwise**, the CPU at the head of the queue (if it is not `c`) releases.
  It first takes the lock with `hold` if it has not yet. It then hands off to
  its successor, linking the successor first if needed, or does a successful
  `cas` if nobody is behind it.

Then:
* `fairM_rely`: every move sequence is valid, so `RelyM` holds for every CPU.
* `fairM_B`: while `c` waits on `busy`, the head releases, so the queue ahead
  of `c` shrinks. `FairB` holds with the zero counter.
* `fairM_N`: while `c` holds the lock with no successor, one links. `FairN`
  holds with the zero counter.
* `acquireM_refines_fair`, `releaseM_refines_fair`: the MCS refinement theorems
  are not vacuous. `demo_mcs`: a contended run, checked by `decide`.
-/

namespace MCS

open ClightL Ticket

/-- Another CPU (NCPU = 8, so there is one). -/
def other (c : CPU) : CPU := if c = 0 then 1 else 0

theorem other_ne (c : CPU) : other c ≠ c := by
  unfold other; by_cases h : c = 0
  · simp [h]
  · simp only [h, ite_false]; exact Ne.symm h
theorem other_lt (c : CPU) : other c < NCPU := by
  unfold other; by_cases h : c = 0 <;> simp [h, NCPU]

def preHold (s : MS) (h : CPU) : List MEvent := if s.ph h = .holding then [] else [⟨h, .hold⟩]

/-- The head `h` releases the lock (taking it first if needed). Nothing is
ever done on behalf of the querying CPU `c`. -/
def relSeq (s : MS) (c h : CPU) : List MEvent :=
  match s.next h with
  | some _ => ⟨h, .handoff⟩ :: preHold s h
  | none =>
    if s.tl = s.hd + 1 then ⟨h, .cas⟩ :: preHold s h
    else match whoAt s (s.hd + 1) with
      | some d => if d = c then preHold s h else ⟨h, .handoff⟩ :: ⟨d, .link⟩ :: preHold s h
      | none => preHold s h

def fairQueryM (c : CPU) (l : MLog) : List MEvent :=
  match mreplay l with
  | none => []
  | some (s, _) =>
    if s.ph c = .holding then
      if s.next c = none then
        if s.tl = s.hd + 1 then [⟨other c, .link⟩, ⟨other c, .swap⟩]
        else match whoAt s (s.hd + 1) with
          | some d => if d = c then [] else [⟨d, .link⟩]
          | none => []
      else []
    else if s.hd < s.tl then
      match whoAt s s.hd with
      | some h => if h = c then [] else relSeq s c h
      | none => []
    else []

theorem whoAt_pos {s : MS} {n : Nat} {p : CPU} (h : whoAt s n = some p) : s.pos p = some n ∧ p < NCPU := by
  obtain ⟨h1, h2⟩ := findCPU_some h
  exact ⟨by simpa using h1, h2⟩

theorem relSeq_cpu {s : MS} {c h : CPU} (hhc : h ≠ c) : ∀ e ∈ relSeq s c h, e.cpu ≠ c := by
  intro e he
  have hpre : ∀ e ∈ preHold s h, e.cpu ≠ c := by
    intro e he; unfold preHold at he; split at he
    · simp at he
    · simp only [List.mem_singleton] at he; subst he; exact hhc
  unfold relSeq at he
  split at he
  · rcases List.mem_cons.1 he with rfl | he
    · exact hhc
    · exact hpre e he
  · split at he
    · rcases List.mem_cons.1 he with rfl | he
      · exact hhc
      · exact hpre e he
    · split at he
      · rename_i d _
        split at he
        · exact hpre e he
        · rename_i hdc
          rcases List.mem_cons.1 he with rfl | he
          · exact hhc
          · rcases List.mem_cons.1 he with rfl | he
            · exact hdc
            · exact hpre e he
      · exact hpre e he

def fairEnvM : MEnv where
  query := fairQueryM
  noSelf := by
    intro c l e he
    simp only [fairQueryM] at he
    split at he
    · simp at he
    · split at he
      · split at he
        · split at he
          · simp at he
            rcases he with rfl | rfl <;> exact other_ne c
          · split at he
            · split at he
              · simp at he
              · rename_i hdc; simp only [List.mem_singleton] at he; subst he; exact hdc
            · simp at he
        · simp at he
      · split at he
        · split at he
          · split at he
            · simp at he
            · rename_i hhc; exact relSeq_cpu hhc e he
          · simp at he
        · simp at he

/-! ## Each move sequence is valid -/

/-- The head takes the lock, if it has not yet. -/
theorem pre_ok {l : MLog} {s : MS} {H : List HEvent} (hl : mreplay l = some (s, H)) {h : CPU}
    (hw : whoAt s s.hd = some h) :
    ∃ s1 H1, mreplay (preHold s h ++ l) = some (s1, H1) ∧ s1.hd = s.hd ∧ s1.tl = s.tl ∧
      s1.pos = s.pos ∧ s1.next = s.next ∧ s1.ph h = .holding ∧ (∀ d, d ≠ h → s1.ph d = s.ph d) := by
  have hi := mreplay_inv hl
  obtain ⟨hp, hN⟩ := whoAt_pos hw
  by_cases hh : s.ph h = .holding
  · exact ⟨s, H, by simp [preHold, hh, hl], rfl, rfl, rfl, rfl, hh, fun _ _ => rfl⟩
  · have hst : mstep s ⟨h, .hold⟩ = some (⟨s.hd, s.tl, s.pos, s.busy, s.next, fset s.ph h .holding⟩,
        some (.acq h)) := by
      rcases hi.head h hp with h1 | h1 | ⟨h1, h2⟩
      · simp [mstep, hN, h1]
      · exact absurd h1 hh
      · simp [mstep, hN, h1, h2]
    refine ⟨⟨s.hd, s.tl, s.pos, s.busy, s.next, fset s.ph h .holding⟩, consOpt (some (.acq h)) H, ?_,
      rfl, rfl, rfl, rfl, by simp, fun d hd => fset_other _ _ hd⟩
    simp only [preHold, hh, ite_false, List.singleton_append]; exact mreplay_cons_of hl hst

/-- The successor at `hd + 1` of a holder `h` without `next` is still linking to `h`. -/
theorem succ_linking {s : MS} (hi : MInv s) {h d : CPU} (hh : s.pos h = some s.hd)
    (hn : s.next h = none) (hd : s.pos d = some (s.hd + 1)) : s.ph d = .linking h := by
  rcases hi.tail d _ hd (by omega) with ⟨p, h1, -, h3, -⟩ | ⟨-, -, p, h3, h4⟩
  · have : p = h := hi.inj p h _ (by simpa using h3) hh
    subst this; exact h1
  · have : p = h := hi.inj p h _ (by simpa using h3) hh
    subst this; rw [hn] at h4; cases h4

theorem rel_ok {l : MLog} {s : MS} {H : List HEvent} (hl : mreplay l = some (s, H)) {c h : CPU}
    (hw : whoAt s s.hd = some h) (hlt : s.hd < s.tl) :
    ∃ s' H', mreplay (relSeq s c h ++ l) = some (s', H') ∧
      ((s.next h ≠ none ∨ s.tl = s.hd + 1 ∨ whoAt s (s.hd + 1) ≠ some c) → s'.hd = s.hd + 1) := by
  have hi := mreplay_inv hl
  obtain ⟨hp, hN⟩ := whoAt_pos hw
  obtain ⟨s1, H1, hr1, e1, e2, e3, e4, e5, e6⟩ := pre_ok hl hw
  have hi1 := mreplay_inv hr1
  unfold relSeq
  cases hnx : s.next h with
  | some d =>
    have hst : mstep s1 ⟨h, .handoff⟩ = some (⟨s1.hd + 1, s1.tl, fset s1.pos h none,
        fset s1.busy d false, s1.next, fset s1.ph h .idle⟩, some (.rel h)) := by
      simp [mstep, hN, e5, e4, hnx]
    exact ⟨_, _, by simpa using mreplay_cons_of hr1 hst, fun _ => by simp [e1]⟩
  | none =>
    by_cases htl : s.tl = s.hd + 1
    · have hst : mstep s1 ⟨h, .cas⟩ = some (⟨s1.hd + 1, s1.tl, fset s1.pos h none, s1.busy, s1.next,
          fset s1.ph h .idle⟩, some (.rel h)) := by
        simp [mstep, hN, e5, e1, e2, htl]
      exact ⟨_, _, by simpa [htl] using mreplay_cons_of hr1 hst, fun _ => by simp [e1]⟩
    · obtain ⟨d, hwd, hpd⟩ := whoAt_some hi (n := s.hd + 1) (by omega) (by omega)
      obtain ⟨-, hdN⟩ := whoAt_pos hwd
      simp only [htl, ite_false, hwd]
      by_cases hdc : d = c
      · subst hdc
        refine ⟨s1, H1, by simpa using hr1, fun hc => ?_⟩
        rcases hc with h1 | h1 | h1 <;> first | exact absurd rfl h1 | exact h1.elim
      · simp only [hdc, ite_false]
        have hlink : s1.ph d = .linking h :=
          succ_linking hi1 (by rw [e3, e1]; exact hp) (by rw [e4]; exact hnx) (by rw [e3, e1]; exact hpd)
        have hst1 : mstep s1 ⟨d, .link⟩ = some (⟨s1.hd, s1.tl, s1.pos, s1.busy, fset s1.next h (some d),
            fset s1.ph d .waiting⟩, none) := by simp [mstep, hdN, hlink]
        have hr2 := mreplay_cons_of hr1 hst1
        have hdh : h ≠ d := fun x => by rw [x, hpd] at hp; simp at hp
        have hst2 : mstep ⟨s1.hd, s1.tl, s1.pos, s1.busy, fset s1.next h (some d), fset s1.ph d .waiting⟩
            ⟨h, .handoff⟩ = some (⟨s1.hd + 1, s1.tl, fset s1.pos h none, fset s1.busy d false,
              fset s1.next h (some d), fset (fset s1.ph d .waiting) h .idle⟩, some (.rel h)) := by
          simp [mstep, hN, fset_other _ _ hdh, e5]
        exact ⟨_, _, by simpa using mreplay_cons_of hr2 hst2, fun _ => by simp [e1]⟩

/-- The holding branch: a successor links. -/
theorem link_ok {l : MLog} {s : MS} {H : List HEvent} (hl : mreplay l = some (s, H)) {c : CPU}
    (hc : c < NCPU) (hh : s.ph c = .holding) (hn : s.next c = none) :
    ∃ s' H', mreplay (fairQueryM c l ++ l) = some (s', H') ∧ s'.next c ≠ none := by
  have hi := mreplay_inv hl
  have hpc := hi.owner_head (.inr (.inl hh))
  by_cases htl : s.tl = s.hd + 1
  · -- nobody behind us: another (idle) CPU swaps in and links
    let d := other c
    have hdc : d ≠ c := other_ne c
    have hdN : d < NCPU := other_lt c
    have hpd : s.pos d = none := by
      cases hp : s.pos d with
      | none => rfl
      | some n =>
        have := hi.bnd d n hp
        have : n = s.hd := by omega
        subst this; exact absurd (hi.inj d c _ hp hpc) hdc
    have hid : s.ph d = .idle := Classical.byContradiction fun hne => by
      obtain ⟨n, hn'⟩ := (hi.inq d).1 hne
      rw [hpd] at hn'; cases hn'
    have ht : tailOf s = some c := (tail_holding hi hh).2 htl
    have hs1 : mstep s ⟨d, .swap⟩ = some (⟨s.hd, s.tl + 1, fset s.pos d (some s.tl), fset s.busy d true,
        fset s.next d none, fset s.ph d (.linking c)⟩, none) := by simp [mstep, hdN, hid, ht]
    have hr1 := mreplay_cons_of hl hs1
    have hs2 : mstep ⟨s.hd, s.tl + 1, fset s.pos d (some s.tl), fset s.busy d true, fset s.next d none,
        fset s.ph d (.linking c)⟩ ⟨d, .link⟩ = some (⟨s.hd, s.tl + 1, fset s.pos d (some s.tl),
          fset s.busy d true, fset (fset s.next d none) c (some d), fset (fset s.ph d (.linking c)) d .waiting⟩,
          none) := by simp [mstep, hdN]
    have hq : fairQueryM c l = [⟨d, .link⟩, ⟨d, .swap⟩] := by simp [fairQueryM, hl, hh, hn, htl, d]
    rw [hq]; exact ⟨_, _, mreplay_cons_of hr1 hs2, by simp⟩
  · obtain ⟨d, hwd, hpd⟩ := whoAt_some hi (n := s.hd + 1) (by have := (hi.bnd c _ hpc).2; omega)
      (by have := (hi.bnd c _ hpc).2; omega)
    obtain ⟨-, hdN⟩ := whoAt_pos hwd
    have hdc : d ≠ c := fun x => by rw [x, hpc] at hpd; simp at hpd
    have hlink := succ_linking hi hpc hn hpd
    have hs1 : mstep s ⟨d, .link⟩ = some (⟨s.hd, s.tl, s.pos, s.busy, fset s.next c (some d),
        fset s.ph d .waiting⟩, none) := by simp [mstep, hdN, hlink]
    have hq : fairQueryM c l = [⟨d, .link⟩] := by simp [fairQueryM, hl, hh, hn, htl, hwd, hdc]
    rw [hq]; exact ⟨_, _, mreplay_cons_of hl hs1, by simp⟩

/-! ## The three properties -/

theorem fairM_rely (c : CPU) (hc : c < NCPU) : RelyM fairEnvM c where
  conform := by
    intro l s H hl
    have hi := mreplay_inv hl
    show ∃ s' h', mreplay (fairQueryM c l ++ l) = some (s', h')
    by_cases hh : s.ph c = .holding
    · by_cases hn : s.next c = none
      · obtain ⟨s', H', hr, -⟩ := link_ok hl hc hh hn; exact ⟨s', H', hr⟩
      · exact ⟨s, H, by simp [fairQueryM, hl, hh, hn]⟩
    · by_cases hlt : s.hd < s.tl
      · obtain ⟨h, hw, -⟩ := whoAt_some hi (n := s.hd) (Nat.le_refl _) hlt
        by_cases hhc : h = c
        · exact ⟨s, H, by simp [fairQueryM, hl, hh, hlt, hw, hhc]⟩
        · obtain ⟨s', H', hr, -⟩ := rel_ok (c := c) hl hw hlt
          exact ⟨s', H', by simpa [fairQueryM, hl, hh, hlt, hw, hhc] using hr⟩
      · exact ⟨s, H, by simp [fairQueryM, hl, hh, hlt]⟩

/-- **The `busy` spin is fair**: the head releases, so the queue ahead shrinks. -/
theorem fairM_B (c : CPU) : FairB fairEnvM c (fun _ => 0) := by
  intro l s H n hl hw hb hn s' H' hr
  left
  have hi := mreplay_inv hl
  have hnh : s.hd < n := by
    rcases Nat.lt_or_eq_of_le (hi.bnd c n hn).1 with h | h
    · exact h
    · subst h; rcases hi.head c hn with h | h | ⟨-, h⟩ <;> simp_all
  have hlt : s.hd < s.tl := by have := (hi.bnd c n hn).2; omega
  obtain ⟨h, hwh, hph⟩ := whoAt_some hi (n := s.hd) (Nat.le_refl _) hlt
  have hhc : h ≠ c := fun x => by subst x; rw [hn] at hph; simp at hph; omega
  have hnh' : s.ph c ≠ .holding := by rw [hw]; simp
  obtain ⟨s2, H2, hr2, hhd⟩ := rel_ok (c := c) hl hwh hlt
  have hq : mpull fairEnvM c l = relSeq s c h ++ l := by
    simp [mpull, fairEnvM, fairQueryM, hl, hnh', hlt, hwh, hhc]
  rw [hq, hr2] at hr; simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨hs2, -⟩ := hr
  subst hs2
  -- `c` is linked behind the head's chain, so the excluded case cannot happen
  have hd' : s2.hd = s.hd + 1 := by
    apply hhd
    by_cases hnx : s.next h = none
    · right
      by_cases htl : s.tl = s.hd + 1
      · exact .inl htl
      · right
        intro hwc
        obtain ⟨hpc, -⟩ := whoAt_pos hwc
        rw [hn] at hpc; simp only [Option.some.injEq] at hpc; subst hpc
        rw [succ_linking hi hph hnx hn] at hw; cases hw
    · exact .inl hnx
  omega

/-- **The `next` spin is fair**: a successor links. -/
theorem fairM_N (c : CPU) (hc : c < NCPU) : FairN fairEnvM c (fun _ => 0) := by
  intro l s H hl hh hn s' H' hr
  left
  obtain ⟨s2, H2, hr2, hne⟩ := link_ok hl hc hh hn
  have hq : mpull fairEnvM c l = fairQueryM c l ++ l := rfl
  rw [hq, hr2] at hr; simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
  exact hne

/-! ## The MCS theorems are not vacuous -/

theorem acquireM_refines_fair {c : CPU} (hc : c < NCPU) {l : MLog} {s : MS} {h : List HEvent}
    (hl : mreplay l = some (s, h)) (hidle : s.ph c = .idle) (loc : Locals) :
    ∃ (εH : HEnv) (loc' : Locals) (r : MLog) (h' : List HEvent),
      HRely εH c ∧ Star (mprims fairEnvM c) ⟨acquireM, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
      hprims εH c .acq [] h = some (0, h') ∧ RelLogM r h' :=
  acquireM_refines_atomic hc (fairM_rely c hc) hl hidle (fun _ => 0) 0 (fun _ => Nat.le_refl _) (fairM_B c) loc

theorem releaseM_refines_fair {c : CPU} (hc : c < NCPU) {l : MLog} {s : MS} {h : List HEvent}
    (hl : mreplay l = some (s, h)) (hh : s.ph c = .holding) (loc : Locals) :
    ∃ (loc' : Locals) (r : MLog),
      Star (mprims fairEnvM c) ⟨releaseM, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
      (∀ εH : HEnv, hprims εH c .rel [] h = some (0, .rel c :: h)) ∧ RelLogM r (.rel c :: h) :=
  releaseM_refines_atomic hc (fairM_rely c hc) hl hh (fun _ => 0) (fairM_N c hc) loc

/-- CPU 1 holds the lock and CPU 2 is linked behind it. CPU 0 enqueues third,
and under `fairEnvM` its acquire completes (checked by evaluation). -/
def contendedM : MLog :=
  [⟨2, .link⟩, ⟨2, .swap⟩, ⟨1, .hold⟩, ⟨1, .swap⟩]

theorem demo_mcs : (acquireSpecM fairEnvM 0 4 contendedM).isSome = true := by decide

end MCS
