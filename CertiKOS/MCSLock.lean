import CertiKOS.MCSProtocol

/-!
# The MCS lock per CPU: C code, guarantee, liveness, and the atomic interface

The per-CPU layer `L0[c]` for the MCS lock, mirroring `TicketLock.lean`,
`TicketProtocol.lean` and `AtomicLayer.lean`.

* `mprims`: the seven primitives. Each is one event, preceded by the
  environment's events. Return values are read off the replayed state:
  `swap` returns the old tail (`0` for none, `p + 1` for CPU `p`), and `cas`
  returns `1` iff the tail is still `c`.
* `acquireM`, `releaseM`: the C code. `acquireSpecM`, `releaseSpecM`: fuel
  specs; `acquireM_sim`, `releaseM_sim`: the code runs them.
* `RelyM`: other CPUs keep the MCS log valid. `FairB`/`FairN`: per-CPU
  fairness for the two spin loops (`CalBound` style). While we wait on `busy`,
  either the queue ahead of us shrinks or a counter drops. While we wait for
  our successor to link, either it links or a counter drops.
* `acquireM_guarantee`, `acquireM_live`: from idle, `acquire` ends holding
  the lock with the single high-level event `acq c`; under `FairB` it returns
  within `NCPU * (K + 1) + K + 1` iterations.
* `releaseM_guarantee`, `releaseM_live`: from holding, `release` ends idle
  with the single high-level event `rel c`.
-/

namespace MCS

open ClightL Ticket

/-! ## The environment and the primitives -/

structure MEnv where
  query : CPU → MLog → List MEvent
  noSelf : ∀ c l e, e ∈ query c l → e.cpu ≠ c

def mpull (ε : MEnv) (c : CPU) (l : MLog) : MLog := ε.query c l ++ l

/-- The protocol state of a log (the initial state if it does not replay). -/
def stOf (l : MLog) : MS := match mreplay l with | some (s, _) => s | none => MS.init

theorem stOf_eq {l : MLog} {s : MS} {h : List HEvent} (hl : mreplay l = some (s, h)) : stOf l = s := by
  simp [stOf, hl]

/-- A CPU as a node pointer: `0` is null. (Ids that would wrap are mapped to `1`;
real CPU ids are below `NCPU`.) -/
def encC : Option CPU → Val
  | none => 0
  | some p => if p + 1 < 2 ^ 32 then BitVec.ofNat 32 (p + 1) else 1

theorem encC_some_ne (p : CPU) : encC (some p) ≠ 0 := by
  simp only [encC]
  split
  · rename_i h; intro h0
    have := congrArg BitVec.toNat h0
    simp [Nat.mod_eq_of_lt h] at this
  · decide

inductive MPrim
  | swap | link | getBusy | hold | getNext | cas | handoff

def mprims (ε : MEnv) (c : CPU) : Prims MPrim MLog
  | .swap, [], l => let l1 := mpull ε c l; some (encC (tailOf (stOf l1)), ⟨c, .swap⟩ :: l1)
  | .link, [], l => some (0, ⟨c, .link⟩ :: mpull ε c l)
  | .getBusy, [], l =>
      let l1 := mpull ε c l; some (if (stOf l1).busy c then 1 else 0, ⟨c, .getBusy⟩ :: l1)
  | .hold, [], l => some (0, ⟨c, .hold⟩ :: mpull ε c l)
  | .getNext, [], l => let l1 := mpull ε c l; some (encC ((stOf l1).next c), ⟨c, .getNext⟩ :: l1)
  | .cas, [], l =>
      let l1 := mpull ε c l; some (if tailOf (stOf l1) = some c then 1 else 0, ⟨c, .cas⟩ :: l1)
  | .handoff, [], l => some (0, ⟨c, .handoff⟩ :: mpull ε c l)
  | _, _, _ => none

/-! ## The C code -/

def loopB : Stmt MPrim := .while (.bin .ne (.var "b") (.const 0)) (.call "b" .getBusy [])
def acquireM : Stmt MPrim :=
  .seq (.call "p" .swap [])
    (.seq (.ite (.bin .ne (.var "p") (.const 0))
        (.seq (.call "_" .link []) (.seq (.call "b" .getBusy []) loopB)) .skip)
      (.call "_" .hold []))

def loopN : Stmt MPrim := .while (.bin .eq (.var "n") (.const 0)) (.call "n" .getNext [])
def releaseM : Stmt MPrim :=
  .seq (.call "n" .getNext [])
    (.ite (.bin .ne (.var "n") (.const 0)) (.call "_" .handoff [])
      (.seq (.call "k" .cas [])
        (.ite (.bin .eq (.var "k") (.const 0))
          (.seq (.call "n" .getNext []) (.seq loopN (.call "_" .handoff []))) .skip)))

/-! ## Specs -/

section Spec
variable (ε : MEnv) (c : CPU)

/-- The `busy` spin: stop when `busy` reads false. -/
def waitB : Nat → Bool → MLog → Option MLog
  | _, false, l => some l
  | 0, true, _ => none
  | f + 1, true, l => waitB f ((stOf (mpull ε c l)).busy c) (⟨c, .getBusy⟩ :: mpull ε c l)

def acquireSpecM (fuel : Nat) (l : MLog) : Option MLog :=
  let l1 := mpull ε c l
  let l2 : MLog := ⟨c, .swap⟩ :: l1
  match tailOf (stOf l1) with
  | none => some (⟨c, .hold⟩ :: mpull ε c l2)
  | some _ =>
    let l3 : MLog := ⟨c, .link⟩ :: mpull ε c l2
    let l4 := mpull ε c l3
    (waitB ε c fuel ((stOf l4).busy c) (⟨c, .getBusy⟩ :: l4)).map fun r => ⟨c, .hold⟩ :: mpull ε c r

/-- The `next` spin after a failed `cas`: stop when `next` is set. -/
def waitN : Nat → Option CPU → MLog → Option MLog
  | _, some _, l => some l
  | 0, none, _ => none
  | f + 1, none, l => waitN f ((stOf (mpull ε c l)).next c) (⟨c, .getNext⟩ :: mpull ε c l)

def releaseSpecM (fuel : Nat) (l : MLog) : Option MLog :=
  let l1 := mpull ε c l
  let l2 : MLog := ⟨c, .getNext⟩ :: l1
  match (stOf l1).next c with
  | some _ => some (⟨c, .handoff⟩ :: mpull ε c l2)
  | none =>
    let l3 := mpull ε c l2
    if tailOf (stOf l3) = some c then some (⟨c, .cas⟩ :: l3)
    else
      let l5 := mpull ε c (⟨c, .cas⟩ :: l3)
      (waitN ε c fuel ((stOf l5).next c) (⟨c, .getNext⟩ :: l5)).map fun r => ⟨c, .handoff⟩ :: mpull ε c r

end Spec

/-! ## Rely and fairness -/

structure RelyM (ε : MEnv) (c : CPU) : Prop where
  conform : ∀ l s h, mreplay l = some (s, h) → ∃ s' h', mreplay (mpull ε c l) = some (s', h')

/-- Fairness of the `busy` spin: while we wait behind the head, either the
queue ahead of us shrinks or the counter drops. -/
def FairB (ε : MEnv) (c : CPU) (bound : MLog → Nat) : Prop :=
  ∀ l s h n, mreplay l = some (s, h) → s.ph c = .waiting → s.busy c = true → s.pos c = some n →
    ∀ s' h', mreplay (mpull ε c l) = some (s', h') →
      n - s.hd > n - s'.hd ∨ bound (⟨c, .getBusy⟩ :: mpull ε c l) < bound l

/-- Fairness of the `next` spin: while our successor has not linked, either it
links or the counter drops. -/
def FairN (ε : MEnv) (c : CPU) (bound : MLog → Nat) : Prop :=
  ∀ l s h, mreplay l = some (s, h) → s.ph c = .holding → s.next c = none →
    ∀ s' h', mreplay (mpull ε c l) = some (s', h') →
      s'.next c ≠ none ∨ bound (⟨c, .getNext⟩ :: mpull ε c l) < bound l

def cpuF (c : CPU) (h : List HEvent) : List HEvent := h.filter fun e => decide (e.cpu = c)

/-! ## Other CPUs' events -/

theorem mstep_other {s s' : MS} {e : MEvent} {o : Option HEvent} {c : CPU} (hi : MInv s)
    (hp : mstep s e = some (s', o)) (hne : e.cpu ≠ c) :
    s'.ph c = s.ph c ∧ s'.pos c = s.pos c ∧ s.hd ≤ s'.hd ∧
      (s.busy c = false → s'.busy c = false) ∧ (s.next c ≠ none → s'.next c = s.next c) ∧
      cpuF c (consOpt o []) = [] := by
  obtain ⟨d, k⟩ := e
  simp only at hne
  have hcd : c ≠ d := Ne.symm hne
  simp only [mstep] at hp
  split at hp
  case isFalse => simp at hp
  cases k <;> cases hph : s.ph d <;> simp only [hph] at hp <;> try simp at hp
  · obtain ⟨rfl, rfl⟩ := hp
    exact ⟨fset_other _ _ hcd, fset_other _ _ hcd, Nat.le_refl _, by simp [fset_other _ _ hcd],
      by simp [fset_other _ _ hcd], rfl⟩
  · -- link: `d` links behind its predecessor `p`; if `p = c`, our `next` was empty
    rename_i p
    obtain ⟨rfl, rfl⟩ := hp
    refine ⟨fset_other _ _ hcd, rfl, Nat.le_refl _, id, fun hn => ?_, rfl⟩
    by_cases hpc : c = p
    · subst hpc
      exfalso; apply hn
      obtain ⟨n, hn'⟩ := (hi.inq d).1 (by rw [hph]; simp)
      have hnh : s.hd < n := by
        rcases Nat.lt_or_eq_of_le (hi.bnd d n hn').1 with h | h
        · exact h
        · subst h; rcases hi.head d hn' with h | h | ⟨h, -⟩ <;> rw [hph] at h <;> cases h
      rcases hi.tail d n hn' hnh with ⟨q, h1, -, -, h4⟩ | ⟨h1, -⟩
      · rw [hph] at h1; cases h1; exact h4
      · rw [hph] at h1; cases h1
    · simp [fset_other _ _ hpc]
  · obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, Nat.le_refl _, id, fun _ => rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hp
    exact ⟨fset_other _ _ hcd, rfl, Nat.le_refl _, id, fun _ => rfl, by simp [cpuF, consOpt, HEvent.cpu, hne]⟩
  · obtain ⟨-, rfl, rfl⟩ := hp
    exact ⟨fset_other _ _ hcd, rfl, Nat.le_refl _, id, fun _ => rfl, by simp [cpuF, consOpt, HEvent.cpu, hne]⟩
  · obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, Nat.le_refl _, id, fun _ => rfl, rfl⟩
  · split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      exact ⟨fset_other _ _ hcd, fset_other _ _ hcd, Nat.le_succ _, id, fun _ => rfl,
        by simp [cpuF, consOpt, HEvent.cpu, hne]⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      exact ⟨rfl, rfl, Nat.le_refl _, id, fun _ => rfl, rfl⟩
  · split at hp
    · rename_i f hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨fset_other _ _ hcd, fset_other _ _ hcd, Nat.le_succ _, fun hb => ?_, fun _ => rfl,
        by simp [cpuF, consOpt, HEvent.cpu, hne]⟩
      by_cases hfc : c = f
      · subst hfc; simp
      · simp [fset_other _ _ hfc, hb]
    · simp at hp

theorem others_eventsM {c : CPU} :
    ∀ (xs : MLog) {l : MLog} {s s' : MS} {h h' : List HEvent},
      (∀ e ∈ xs, e.cpu ≠ c) → mreplay l = some (s, h) → mreplay (xs ++ l) = some (s', h') →
      s'.ph c = s.ph c ∧ s'.pos c = s.pos c ∧ s.hd ≤ s'.hd ∧
      (s.busy c = false → s'.busy c = false) ∧ (s.next c ≠ none → s'.next c = s.next c) ∧
      cpuF c h' = cpuF c h
  | [], l, s, s', h, h', _, hl, hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr
    exact ⟨rfl, rfl, Nat.le_refl _, id, fun _ => rfl, rfl⟩
  | e :: xs, l, s, s', h, h', hx, hl, hr => by
    obtain ⟨s2, h2, o, hl2, hp, rfl⟩ := mreplay_cons hr
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ :=
      others_eventsM xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := mstep_other (mreplay_inv hl2) hp (hx e List.mem_cons_self)
    refine ⟨j1.trans i1, j2.trans i2, Nat.le_trans i3 j3, fun hb => j4 (i4 hb),
      fun hn => (j5 (by rw [i5 hn]; exact hn)).trans (i5 hn), ?_⟩
    cases o with
    | none => exact i6
    | some he =>
      simp only [consOpt, cpuF, List.filter_cons] at j6 ⊢
      split at j6 <;> simp_all [cpuF]

theorem pull_othersM {ε : MEnv} {c : CPU} (hR : RelyM ε c) {l : MLog} {s : MS} {h : List HEvent}
    (hl : mreplay l = some (s, h)) :
    ∃ s' h', mreplay (mpull ε c l) = some (s', h') ∧ s'.ph c = s.ph c ∧ s'.pos c = s.pos c ∧
      s.hd ≤ s'.hd ∧ (s.busy c = false → s'.busy c = false) ∧
      (s.next c ≠ none → s'.next c = s.next c) ∧ cpuF c h' = cpuF c h := by
  obtain ⟨s', h', hr⟩ := hR.conform l s h hl
  exact ⟨s', h', hr, others_eventsM _ (ε.noSelf c l) hl hr⟩

/-! ## `acquire`: guarantee and bounded liveness -/

section Acq
variable (ε : MEnv) (c : CPU) (h₀ : List HEvent)

/-- The `busy` spin: we wait in the queue, `b` is what we last read. -/
def LoopB (l : MLog) (b : Bool) : Prop :=
  ∃ s h n, mreplay l = some (s, h) ∧ s.ph c = .waiting ∧ s.pos c = some n ∧ s.busy c = b ∧
    cpuF c h = cpuF c h₀

theorem after_getBusy (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {b : Bool} (hi : LoopB c h₀ l b) :
    LoopB c h₀ (⟨c, .getBusy⟩ :: mpull ε c l) ((stOf (mpull ε c l)).busy c) := by
  obtain ⟨s, h, n, hl, hw, hn, -, hf⟩ := hi
  obtain ⟨s1, h1, hr1, hph1, hpos1, -, -, -, hf1⟩ := pull_othersM hR hl
  have hw1 : s1.ph c = .waiting := by rw [hph1]; exact hw
  have hp : mstep s1 ⟨c, .getBusy⟩ = some (s1, none) := by simp [mstep, hc, hw1]
  exact ⟨s1, h1, n, by simpa [consOpt] using mreplay_cons_of hr1 hp, hw1, by rw [hpos1]; exact hn,
    by rw [stOf_eq hr1], hf1.trans hf⟩

theorem waitB_guar (hc : c < NCPU) (hR : RelyM ε c) :
    ∀ f b l r, LoopB c h₀ l b → waitB ε c f b l = some r → LoopB c h₀ r false := by
  intro f
  induction f with
  | zero =>
    intro b l r hi hw
    cases b
    · simp [waitB] at hw; subst hw; exact hi
    · simp [waitB] at hw
  | succ f ih =>
    intro b l r hi hw
    cases b
    · simp [waitB] at hw; subst hw; exact hi
    · simp only [waitB] at hw
      exact ih _ _ r (after_getBusy ε c h₀ hc hR hi) hw

theorem waitB_live (hc : c < NCPU) (hR : RelyM ε c) (bound : MLog → Nat) (K : Nat)
    (hK : ∀ l, bound l ≤ K) (hF : FairB ε c bound) :
    ∀ m bb l b, LoopB c h₀ l b → (∀ s h n, mreplay l = some (s, h) → s.pos c = some n → n - s.hd = m) →
      bound l = bb → ∃ f r, f ≤ m * (K + 1) + bb ∧ waitB ε c f b l = some r := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro bb
  induction bb using Nat.strongRecOn with
  | _ bb ihb =>
  intro l b hi hm hb
  cases b
  · exact ⟨0, l, Nat.zero_le _, by simp [waitB]⟩
  · obtain ⟨s, h, n, hl, hw, hn, hbt, hf⟩ := hi
    obtain ⟨s1, h1, hr1, hph1, hpos1, hhd, -, -, -⟩ := pull_othersM hR hl
    have hi' := after_getBusy ε c h₀ hc hR ⟨s, h, n, hl, hw, hn, hbt, hf⟩
    let l' : MLog := ⟨c, .getBusy⟩ :: mpull ε c l
    have hp1 : mstep s1 ⟨c, .getBusy⟩ = some (s1, none) := by
      simp [mstep, hc, (by rw [hph1]; exact hw : s1.ph c = .waiting)]
    have hl' : mreplay l' = some (s1, h1) := by simpa [consOpt] using mreplay_cons_of hr1 hp1
    have hm' : ∀ s2 h2 n2, mreplay l' = some (s2, h2) → s2.pos c = some n2 → n2 - s2.hd = n - s1.hd := by
      intro s2 h2 n2 h2' hn2
      rw [hl'] at h2'; simp only [Option.some.injEq, Prod.mk.injEq] at h2'; obtain ⟨rfl, -⟩ := h2'
      rw [hpos1, hn] at hn2; simp only [Option.some.injEq] at hn2; subst hn2; rfl
    have hmm := hm s h n hl hn
    have hfair := hF l s h n hl hw hbt hn s1 h1 hr1
    have step_eq : ∀ f, waitB ε c (f + 1) true l = waitB ε c f ((stOf (mpull ε c l)).busy c) l' := by
      intro f; rfl
    by_cases hlt : n - s1.hd < m
    · obtain ⟨f, r, hfle, hwr⟩ := ihm _ hlt (bound l') l' _ hi' hm' rfl
      have h1 := Nat.mul_le_mul_right (K + 1) (show n - s1.hd + 1 ≤ m by omega)
      rw [Nat.succ_mul] at h1
      have h2 := hK l'
      exact ⟨f + 1, r, by omega, by rw [step_eq]; exact hwr⟩
    · have hb' : bound l' < bb := by
        rcases hfair with h1 | h1
        · omega
        · rw [← hb]; exact h1
      have hm'' : ∀ s2 h2 n2, mreplay l' = some (s2, h2) → s2.pos c = some n2 → n2 - s2.hd = m := by
        intro s2 h2 n2 h2' hn2; rw [hm' s2 h2 n2 h2' hn2]; omega
      obtain ⟨f, r, hfle, hwr⟩ := ihb _ hb' l' _ hi' hm'' rfl
      exact ⟨f + 1, r, by omega, by rw [step_eq]; exact hwr⟩

end Acq

/-- After `acquire`: `c` holds the lock, and its only new high-level event is
`acq c` on top. -/
def AcqPostM (c : CPU) (h₀ : List HEvent) (r : MLog) : Prop :=
  ∃ s h₁, mreplay r = some (s, .acq c :: h₁) ∧ s.ph c = .holding ∧ cpuF c h₁ = cpuF c h₀

theorem hold_from {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {r : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay r = some (s, h))
    (hown : s.ph c = .front ∨ (s.ph c = .waiting ∧ s.busy c = false)) :
    AcqPostM c h (⟨c, .hold⟩ :: mpull ε c r) := by
  obtain ⟨s1, h1, hr1, hph1, -, -, hb1, -, hf1⟩ := pull_othersM hR hl
  rcases hown with hfr | ⟨hw, hb⟩
  · have hfr1 : s1.ph c = .front := by rw [hph1]; exact hfr
    have hp : mstep s1 ⟨c, .hold⟩ = some (⟨s1.hd, s1.tl, s1.pos, s1.busy, s1.next, fset s1.ph c .holding⟩,
        some (.acq c)) := by simp [mstep, hc, hfr1]
    exact ⟨_, h1, mreplay_cons_of hr1 hp, by simp, hf1⟩
  · have hw1 : s1.ph c = .waiting := by rw [hph1]; exact hw
    have hp : mstep s1 ⟨c, .hold⟩ = some (⟨s1.hd, s1.tl, s1.pos, s1.busy, s1.next, fset s1.ph c .holding⟩,
        some (.acq c)) := by simp [mstep, hc, hw1, hb1 hb]
    exact ⟨_, h1, mreplay_cons_of hr1 hp, by simp, hf1⟩

/-- The state right after our `swap` (and, if we have a predecessor, `link`). -/
theorem acq_enter {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay l = some (s, h)) (hidle : s.ph c = .idle) :
    (tailOf (stOf (mpull ε c l)) = none →
      ∃ s2 h2, mreplay (⟨c, .swap⟩ :: mpull ε c l) = some (s2, h2) ∧ s2.ph c = .front ∧ cpuF c h2 = cpuF c h) ∧
    (∀ p, tailOf (stOf (mpull ε c l)) = some p →
      LoopB c h (⟨c, .getBusy⟩ :: mpull ε c (⟨c, .link⟩ :: mpull ε c (⟨c, .swap⟩ :: mpull ε c l)))
        ((stOf (mpull ε c (⟨c, .link⟩ :: mpull ε c (⟨c, .swap⟩ :: mpull ε c l)))).busy c)) := by
  obtain ⟨s1, h1, hr1, hph1, -, -, -, -, hf1⟩ := pull_othersM hR hl
  have hid1 : s1.ph c = .idle := by rw [hph1]; exact hidle
  have hst1 := stOf_eq hr1
  have hsw : mstep s1 ⟨c, .swap⟩ = some (⟨s1.hd, s1.tl + 1, fset s1.pos c (some s1.tl),
      fset s1.busy c true, fset s1.next c none,
      fset s1.ph c (match tailOf s1 with | none => .front | some p => .linking p)⟩, none) := by
    simp [mstep, hc, hid1] <;> rfl
  have hr2 := mreplay_cons_of hr1 hsw
  refine ⟨fun ht => ⟨_, _, hr2, by rw [hst1] at ht; simp [ht], by simpa [consOpt] using hf1⟩, fun p ht => ?_⟩
  rw [hst1] at ht
  -- link
  obtain ⟨s3, h3, hr3, hph3, hpos3, -, -, -, hf3⟩ := pull_othersM hR hr2
  have hl3 : s3.ph c = .linking p := by rw [hph3]; simp [ht]
  have hlk : mstep s3 ⟨c, .link⟩ = some (⟨s3.hd, s3.tl, s3.pos, s3.busy, fset s3.next p (some c),
      fset s3.ph c .waiting⟩, none) := by simp [mstep, hc, hl3]
  have hr4 := mreplay_cons_of hr3 hlk
  refine after_getBusy ε c h hc hR ⟨_, _, s1.tl, hr4, by simp, ?_, rfl, ?_⟩
  · show s3.pos c = some s1.tl; rw [hpos3]; simp
  · simpa [consOpt] using hf3.trans (by simpa [consOpt] using hf1)

theorem acquireM_guarantee {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay l = some (s, h)) (hidle : s.ph c = .idle) {fuel : Nat} {r : MLog}
    (hspec : acquireSpecM ε c fuel l = some r) : AcqPostM c h r := by
  obtain ⟨hnone, hsome⟩ := acq_enter hc hR hl hidle
  simp only [acquireSpecM] at hspec
  split at hspec
  · rename_i ht
    simp only [Option.some.injEq] at hspec; subst hspec
    obtain ⟨s2, h2, hr2, hfr, hf2⟩ := hnone ht
    obtain ⟨s', h₁, hr', hhold, hf'⟩ := hold_from hc hR hr2 (.inl hfr)
    exact ⟨s', h₁, hr', hhold, hf'.trans hf2⟩
  · rename_i p ht
    simp only [Option.map_eq_some_iff] at hspec
    obtain ⟨r0, hw, rfl⟩ := hspec
    obtain ⟨s0, h0, n0, hr0, hw0, -, hb0, hf0⟩ := waitB_guar ε c h hc hR _ _ _ r0 (hsome p ht) hw
    obtain ⟨s', h₁, hr', hhold, hf'⟩ := hold_from hc hR hr0 (.inr ⟨hw0, hb0⟩)
    exact ⟨s', h₁, hr', hhold, hf'.trans hf0⟩

/-- **Bounded liveness of `acquire`**: under `FairB` with a counter bounded by
`K`, the spec returns within `m * (K + 1) + K` iterations, where `m` is how
far back in the queue we enter. -/
theorem acquireM_live {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay l = some (s, h)) (hidle : s.ph c = .idle)
    (bound : MLog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K) (hF : FairB ε c bound) :
    ∃ fuel r, acquireSpecM ε c fuel l = some r := by
  obtain ⟨-, hsome⟩ := acq_enter hc hR hl hidle
  cases ht : tailOf (stOf (mpull ε c l)) with
  | none => exact ⟨0, ⟨c, .hold⟩ :: mpull ε c (⟨c, .swap⟩ :: mpull ε c l), by simp [acquireSpecM, ht]⟩
  | some p =>
    have hi := hsome p ht
    obtain ⟨s4, h4, n4, hr4, -, hn4, -, -⟩ := hsome p ht
    obtain ⟨f, r, -, hw⟩ := waitB_live ε c h hc hR bound K hK hF (n4 - s4.hd) _ _ _ hi
      (fun s2 h2 n2 h2' hn2 => by
        rw [hr4] at h2'; simp only [Option.some.injEq, Prod.mk.injEq] at h2'; obtain ⟨rfl, -⟩ := h2'
        rw [hn4] at hn2; simp only [Option.some.injEq] at hn2; subst hn2; rfl) rfl
    exact ⟨f, ⟨c, .hold⟩ :: mpull ε c r, by simp [acquireSpecM, ht, hw]⟩

/-! ## `release`: guarantee and liveness -/

/-- After `release`: `c` is idle, and its only new high-level event is `rel c`. -/
def RelPostM (c : CPU) (h₀ : List HEvent) (r : MLog) : Prop :=
  ∃ s h₁, mreplay r = some (s, .rel c :: h₁) ∧ s.ph c = .idle ∧ cpuF c h₁ = cpuF c h₀

/-- With the lock held, the tail is still ours exactly when nobody queued behind us. -/
theorem tail_holding {s : MS} (hi : MInv s) {c : CPU} (hh : s.ph c = .holding) :
    tailOf s = some c ↔ s.tl = s.hd + 1 := by
  have hpc := hi.owner_head (.inr (.inl hh))
  have hlt := (hi.bnd c _ hpc).2
  constructor
  · intro ht
    simp only [tailOf, hlt, ite_true] at ht
    have hp := (findCPU_some ht).1
    simp only [beq_iff_eq] at hp
    rw [hpc] at hp; simp only [Option.some.injEq] at hp; omega
  · intro htl
    obtain ⟨p, hw, hp⟩ := whoAt_some hi (n := s.tl - 1) (by omega) (by omega)
    have : p = c := hi.inj p c _ hp (by rw [hpc]; congr 1; omega)
    subst this
    simp [tailOf, hlt, hw]

section Rel
variable (ε : MEnv) (c : CPU) (h₀ : List HEvent)

/-- Holding the lock, and `nx` is what we last read of `next[c]`. -/
def LoopN (l : MLog) (nx : Option CPU) : Prop :=
  ∃ s h, mreplay l = some (s, h) ∧ s.ph c = .holding ∧ s.next c = nx ∧ cpuF c h = cpuF c h₀

theorem after_getNext (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {nx : Option CPU}
    (hi : LoopN c h₀ l nx) : LoopN c h₀ (⟨c, .getNext⟩ :: mpull ε c l) ((stOf (mpull ε c l)).next c) := by
  obtain ⟨s, h, hl, hh, -, hf⟩ := hi
  obtain ⟨s1, h1, hr1, hph1, -, -, -, -, hf1⟩ := pull_othersM hR hl
  have hh1 : s1.ph c = .holding := by rw [hph1]; exact hh
  have hp : mstep s1 ⟨c, .getNext⟩ = some (s1, none) := by simp [mstep, hc, hh1]
  exact ⟨s1, h1, by simpa [consOpt] using mreplay_cons_of hr1 hp, hh1, by rw [stOf_eq hr1],
    hf1.trans hf⟩

theorem waitN_guar (hc : c < NCPU) (hR : RelyM ε c) :
    ∀ f nx l r, LoopN c h₀ l nx → waitN ε c f nx l = some r → ∃ d, LoopN c h₀ r (some d) := by
  intro f
  induction f with
  | zero =>
    intro nx l r hi hw
    cases nx with
    | none => simp [waitN] at hw
    | some d => simp [waitN] at hw; subst hw; exact ⟨d, hi⟩
  | succ f ih =>
    intro nx l r hi hw
    cases nx with
    | none => simp only [waitN] at hw; exact ih _ _ r (after_getNext ε c h₀ hc hR hi) hw
    | some d => simp [waitN] at hw; subst hw; exact ⟨d, hi⟩

theorem waitN_live (hc : c < NCPU) (hR : RelyM ε c) (bound : MLog → Nat) (hF : FairN ε c bound) :
    ∀ bb l nx, LoopN c h₀ l nx → bound l = bb → ∃ f r, f ≤ bb + 1 ∧ waitN ε c f nx l = some r := by
  intro bb
  induction bb using Nat.strongRecOn with
  | _ bb ihb =>
  intro l nx hi hb
  cases nx with
  | some d => exact ⟨0, l, Nat.zero_le _, by simp [waitN]⟩
  | none =>
    obtain ⟨s, h, hl, hh, hn, hf⟩ := hi
    obtain ⟨s1, h1, hr1, -, -, -, -, -, -⟩ := pull_othersM hR hl
    have hi' := after_getNext ε c h₀ hc hR ⟨s, h, hl, hh, hn, hf⟩
    have step_eq : ∀ f, waitN ε c (f + 1) none l =
        waitN ε c f ((stOf (mpull ε c l)).next c) (⟨c, .getNext⟩ :: mpull ε c l) := fun f => rfl
    rcases hF l s h hl hh hn s1 h1 hr1 with hset | hlt
    · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hset
      exact ⟨1, ⟨c, .getNext⟩ :: mpull ε c l, by omega, by rw [step_eq, stOf_eq hr1, hd]; simp [waitN]⟩
    · obtain ⟨f, r, hfle, hw⟩ := ihb _ (by rw [← hb]; exact hlt) _ _ hi' rfl
      exact ⟨f + 1, r, by omega, by rw [step_eq]; exact hw⟩

end Rel

theorem handoff_from {ε : MEnv} {c : CPU} {h₀ : List HEvent} (hc : c < NCPU) (hR : RelyM ε c) {r : MLog}
    {d : CPU} (hi : LoopN c h₀ r (some d)) : RelPostM c h₀ (⟨c, .handoff⟩ :: mpull ε c r) := by
  obtain ⟨s, h, hl, hh, hn, hf⟩ := hi
  obtain ⟨s1, h1, hr1, hph1, -, -, -, hn1, hf1⟩ := pull_othersM hR hl
  have hh1 : s1.ph c = .holding := by rw [hph1]; exact hh
  have hn1' : s1.next c = some d := by rw [hn1 (by rw [hn]; simp), hn]
  have hp : mstep s1 ⟨c, .handoff⟩ = some (⟨s1.hd + 1, s1.tl, fset s1.pos c none,
      fset s1.busy d false, s1.next, fset s1.ph c .idle⟩, some (.rel c)) := by
    simp [mstep, hc, hh1, hn1']
  exact ⟨_, h1, mreplay_cons_of hr1 hp, by simp, hf1.trans hf⟩

theorem releaseM_guarantee {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay l = some (s, h)) (hh : s.ph c = .holding) {fuel : Nat} {r : MLog}
    (hspec : releaseSpecM ε c fuel l = some r) : RelPostM c h r := by
  have hi0 : LoopN c h l (s.next c) := ⟨s, h, hl, hh, rfl, rfl⟩
  have hi1 := after_getNext ε c h hc hR hi0
  simp only [releaseSpecM] at hspec
  split at hspec
  · rename_i d hd
    simp only [Option.some.injEq] at hspec; subst hspec
    rw [hd] at hi1; exact handoff_from hc hR hi1
  · rename_i hd
    rw [hd] at hi1
    obtain ⟨s2, h2, hl2, hh2, hn2, hf2⟩ := hi1
    obtain ⟨s3, h3, hr3, hph3, -, -, -, -, hf3⟩ := pull_othersM hR hl2
    have hh3 : s3.ph c = .holding := by rw [hph3]; exact hh2
    have hi3 := mreplay_inv hr3
    rw [stOf_eq hr3] at hspec
    split at hspec
    · -- the CAS succeeds: nobody is behind us
      rename_i ht
      simp only [Option.some.injEq] at hspec; subst hspec
      have htl := (tail_holding hi3 hh3).1 ht
      have hp : mstep s3 ⟨c, .cas⟩ = some (⟨s3.hd + 1, s3.tl, fset s3.pos c none, s3.busy, s3.next,
          fset s3.ph c .idle⟩, some (.rel c)) := by simp [mstep, hc, hh3, htl]
      exact ⟨_, h3, mreplay_cons_of hr3 hp, by simp, hf3.trans hf2⟩
    · -- the CAS fails: wait for our successor, then hand off
      rename_i ht
      have htl : ¬ s3.tl = s3.hd + 1 := fun h' => ht ((tail_holding hi3 hh3).2 h')
      have hp : mstep s3 ⟨c, .cas⟩ = some (s3, none) := by simp [mstep, hc, hh3, htl]
      have hl4 := mreplay_cons_of hr3 hp
      have hi4 : LoopN c h (⟨c, .cas⟩ :: mpull ε c (⟨c, .getNext⟩ :: mpull ε c l)) (s3.next c) :=
        ⟨s3, h3, by simpa [consOpt] using hl4, hh3, rfl, hf3.trans hf2⟩
      have hi5 := after_getNext ε c h hc hR hi4
      simp only [Option.map_eq_some_iff] at hspec
      obtain ⟨r0, hw, rfl⟩ := hspec
      obtain ⟨d, hd'⟩ := waitN_guar ε c h hc hR _ _ _ r0 hi5 hw
      exact handoff_from hc hR hd'

theorem releaseM_live {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay l = some (s, h)) (hh : s.ph c = .holding)
    (bound : MLog → Nat) (hF : FairN ε c bound) : ∃ fuel r, releaseSpecM ε c fuel l = some r := by
  have hi1 := after_getNext ε c h hc hR ⟨s, h, hl, hh, rfl, rfl⟩
  cases hd : (stOf (mpull ε c l)).next c with
  | some d => exact ⟨0, ⟨c, .handoff⟩ :: mpull ε c (⟨c, .getNext⟩ :: mpull ε c l), by simp [releaseSpecM, hd]⟩
  | none =>
    rw [hd] at hi1
    obtain ⟨s2, h2, hl2, hh2, -, hf2⟩ := hi1
    obtain ⟨s3, h3, hr3, hph3, -, -, -, -, hf3⟩ := pull_othersM hR hl2
    have hh3 : s3.ph c = .holding := by rw [hph3]; exact hh2
    by_cases ht : tailOf (stOf (mpull ε c (⟨c, .getNext⟩ :: mpull ε c l))) = some c
    · exact ⟨0, ⟨c, .cas⟩ :: mpull ε c (⟨c, .getNext⟩ :: mpull ε c l), by simp [releaseSpecM, hd, ht]⟩
    · rw [stOf_eq hr3] at ht
      have htl : ¬ s3.tl = s3.hd + 1 := fun h' => ht ((tail_holding (mreplay_inv hr3) hh3).2 h')
      have hp : mstep s3 ⟨c, .cas⟩ = some (s3, none) := by simp [mstep, hc, hh3, htl]
      have hi4 : LoopN c h (⟨c, .cas⟩ :: mpull ε c (⟨c, .getNext⟩ :: mpull ε c l)) (s3.next c) :=
        ⟨s3, h3, by simpa [consOpt] using mreplay_cons_of hr3 hp, hh3, rfl, hf3.trans hf2⟩
      have hi5 := after_getNext ε c h hc hR hi4
      obtain ⟨f, r, -, hw⟩ := waitN_live ε c h hc hR bound hF _ _ _ hi5 rfl
      refine ⟨f, ⟨c, .handoff⟩ :: mpull ε c r, ?_⟩
      simp [releaseSpecM, hd, stOf_eq hr3, ht, hw]

/-! ## The C code runs the specs -/

theorem loopB_sim (ε : MEnv) (c : CPU) :
    ∀ (f : Nat) (b : Bool) (σ : Locals) (l r : MLog) (k : Cont MPrim),
      σ "b" = (if b then 1 else 0) → waitB ε c f b l = some r →
      ∃ σ', Star (mprims ε c) ⟨loopB, k, σ, l⟩ ⟨.skip, k, σ', r⟩ := by
  intro f
  induction f with
  | zero =>
    intro b σ l r k hb hw
    cases b
    · simp [waitB] at hw; subst hw
      exact ⟨σ, Star.single (by simp [step, loopB, Expr.eval, BinOp.eval, hb])⟩
    · simp [waitB] at hw
  | succ f ih =>
    intro b σ l r k hb hw
    cases b
    · simp [waitB] at hw; subst hw
      exact ⟨σ, Star.single (by simp [step, loopB, Expr.eval, BinOp.eval, hb])⟩
    · simp only [waitB] at hw
      let l1 := mpull ε c l
      let σ1 := σ.set "b" (if (stOf l1).busy c then 1 else 0)
      obtain ⟨σ', hst⟩ := ih _ σ1 (⟨c, .getBusy⟩ :: l1) r k (by simp [σ1, l1]) hw
      refine ⟨σ', .step (c' := ⟨.call "b" .getBusy [], .loop (.bin .ne (.var "b") (.const 0))
        (.call "b" .getBusy []) k, σ, l⟩) (by simp [step, loopB, Expr.eval, BinOp.eval, hb]) ?_⟩
      refine .step (c' := ⟨.skip, .loop (.bin .ne (.var "b") (.const 0)) (.call "b" .getBusy []) k,
        σ1, ⟨c, .getBusy⟩ :: l1⟩) (by simp [step, mprims, σ1, l1]) ?_
      exact .step (c' := ⟨loopB, k, σ1, ⟨c, .getBusy⟩ :: l1⟩) (by simp [step, loopB]) hst

theorem acquireM_sim (ε : MEnv) (c : CPU) (fuel : Nat) (σ : Locals) (l r : MLog) (k : Cont MPrim)
    (h : acquireSpecM ε c fuel l = some r) :
    ∃ σ', Star (mprims ε c) ⟨acquireM, k, σ, l⟩ ⟨.skip, k, σ', r⟩ := by
  let l1 := mpull ε c l
  let l2 : MLog := ⟨c, .swap⟩ :: l1
  let σ1 := σ.set "p" (encC (tailOf (stOf l1)))
  let ite' : Stmt MPrim := .ite (.bin .ne (.var "p") (.const 0))
    (.seq (.call "_" .link []) (.seq (.call "b" .getBusy []) loopB)) .skip
  have h0 : Star (mprims ε c) ⟨acquireM, k, σ, l⟩ ⟨ite', .seq (.call "_" .hold []) k, σ1, l2⟩ := by
    refine .step (c' := ⟨.call "p" .swap [], .seq (.seq ite' (.call "_" .hold [])) k, σ, l⟩)
      (by simp [step, acquireM, ite']) ?_
    refine .step (c' := ⟨.skip, .seq (.seq ite' (.call "_" .hold [])) k, σ1, l2⟩)
      (by simp [step, mprims, σ1, l2, l1]) ?_
    refine .step (c' := ⟨.seq ite' (.call "_" .hold []), k, σ1, l2⟩) (by simp [step]) ?_
    exact .single (by simp [step])
  simp only [acquireSpecM] at h
  split at h
  · rename_i ht
    simp only [Option.some.injEq] at h; subst h
    refine ⟨σ1.set "_" 0, h0.trans ?_⟩
    refine .step (c' := ⟨.skip, .seq (.call "_" .hold []) k, σ1, l2⟩)
      (by simp [step, ite', Expr.eval, BinOp.eval, σ1, l1, ht, encC]) ?_
    refine .step (c' := ⟨.call "_" .hold [], k, σ1, l2⟩) (by simp [step]) ?_
    exact .single (by simp [step, mprims, l2, l1])
  · rename_i q ht
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r0, hw, rfl⟩ := h
    let l3 : MLog := ⟨c, .link⟩ :: mpull ε c l2
    let l4 := mpull ε c l3
    let σ2 := (σ1.set "_" 0).set "b" (if (stOf l4).busy c then 1 else 0)
    obtain ⟨σ3, hloop⟩ := loopB_sim ε c fuel ((stOf l4).busy c) σ2 (⟨c, .getBusy⟩ :: l4) r0 (.seq (.call "_" .hold []) k)
      (by simp [σ2]) (by simpa [l4, l3, l2, l1] using hw)
    refine ⟨σ3.set "_" 0, h0.trans ?_⟩
    have hp : encC (tailOf (stOf l1)) ≠ 0 := by simp only [l1]; rw [ht]; exact encC_some_ne q
    refine .step (c' := ⟨.seq (.call "_" .link []) (.seq (.call "b" .getBusy []) loopB),
      .seq (.call "_" .hold []) k, σ1, l2⟩) (by simp [step, ite', Expr.eval, BinOp.eval, σ1]; exact hp) ?_
    refine .step (c' := ⟨.call "_" .link [], .seq (.seq (.call "b" .getBusy []) loopB)
      (.seq (.call "_" .hold []) k), σ1, l2⟩) (by simp [step]) ?_
    refine .step (c' := ⟨.skip, .seq (.seq (.call "b" .getBusy []) loopB) (.seq (.call "_" .hold []) k),
      σ1.set "_" 0, l3⟩) (by simp [step, mprims, l3]) ?_
    refine .step (c' := ⟨.seq (.call "b" .getBusy []) loopB, .seq (.call "_" .hold []) k, σ1.set "_" 0, l3⟩)
      (by simp [step]) ?_
    refine .step (c' := ⟨.call "b" .getBusy [], .seq loopB (.seq (.call "_" .hold []) k), σ1.set "_" 0, l3⟩)
      (by simp [step]) ?_
    refine .step (c' := ⟨.skip, .seq loopB (.seq (.call "_" .hold []) k), σ2, ⟨c, .getBusy⟩ :: l4⟩)
      (by simp [step, mprims, σ2, l4]) ?_
    refine .step (c' := ⟨loopB, .seq (.call "_" .hold []) k, σ2, ⟨c, .getBusy⟩ :: l4⟩) (by simp [step]) ?_
    refine hloop.trans ?_
    refine .step (c' := ⟨.call "_" .hold [], k, σ3, r0⟩) (by simp [step]) ?_
    exact .single (by simp [step, mprims])

theorem loopN_sim (ε : MEnv) (c : CPU) :
    ∀ (f : Nat) (nx : Option CPU) (σ : Locals) (l r : MLog) (k : Cont MPrim),
      σ "n" = encC nx → waitN ε c f nx l = some r →
      ∃ σ', Star (mprims ε c) ⟨loopN, k, σ, l⟩ ⟨.skip, k, σ', r⟩ := by
  intro f
  induction f with
  | zero =>
    intro nx σ l r k hn hw
    cases nx with
    | none => simp [waitN] at hw
    | some d =>
      simp [waitN] at hw; subst hw
      exact ⟨σ, Star.single (by simp [step, loopN, Expr.eval, BinOp.eval, hn]; exact encC_some_ne _)⟩
  | succ f ih =>
    intro nx σ l r k hn hw
    cases nx with
    | some d =>
      simp [waitN] at hw; subst hw
      exact ⟨σ, Star.single (by simp [step, loopN, Expr.eval, BinOp.eval, hn]; exact encC_some_ne _)⟩
    | none =>
      simp only [waitN] at hw
      let l1 := mpull ε c l
      let σ1 := σ.set "n" (encC ((stOf l1).next c))
      obtain ⟨σ', hst⟩ := ih _ σ1 (⟨c, .getNext⟩ :: l1) r k (by simp [σ1, l1]) hw
      refine ⟨σ', .step (c' := ⟨.call "n" .getNext [], .loop (.bin .eq (.var "n") (.const 0))
        (.call "n" .getNext []) k, σ, l⟩) (by simp [step, loopN, Expr.eval, BinOp.eval, hn, encC]) ?_⟩
      refine .step (c' := ⟨.skip, .loop (.bin .eq (.var "n") (.const 0)) (.call "n" .getNext []) k,
        σ1, ⟨c, .getNext⟩ :: l1⟩) (by simp [step, mprims, σ1, l1]) ?_
      exact .step (c' := ⟨loopN, k, σ1, ⟨c, .getNext⟩ :: l1⟩) (by simp [step, loopN]) hst

theorem releaseM_sim (ε : MEnv) (c : CPU) (fuel : Nat) (σ : Locals) (l r : MLog) (k : Cont MPrim)
    (h : releaseSpecM ε c fuel l = some r) :
    ∃ σ', Star (mprims ε c) ⟨releaseM, k, σ, l⟩ ⟨.skip, k, σ', r⟩ := by
  let l1 := mpull ε c l
  let l2 : MLog := ⟨c, .getNext⟩ :: l1
  let σ1 := σ.set "n" (encC ((stOf l1).next c))
  let tail' : Stmt MPrim := .seq (.call "k" .cas [])
    (.ite (.bin .eq (.var "k") (.const 0)) (.seq (.call "n" .getNext []) (.seq loopN (.call "_" .handoff []))) .skip)
  have h0 : Star (mprims ε c) ⟨releaseM, k, σ, l⟩
      ⟨.ite (.bin .ne (.var "n") (.const 0)) (.call "_" .handoff []) tail', k, σ1, l2⟩ := by
    refine .step (c' := ⟨.call "n" .getNext [], .seq (.ite (.bin .ne (.var "n") (.const 0))
      (.call "_" .handoff []) tail') k, σ, l⟩) (by simp [step, releaseM, tail']) ?_
    refine .step (c' := ⟨.skip, .seq (.ite (.bin .ne (.var "n") (.const 0)) (.call "_" .handoff []) tail') k,
      σ1, l2⟩) (by simp [step, mprims, σ1, l2, l1]) ?_
    exact .single (by simp [step])
  simp only [releaseSpecM] at h
  split at h
  · rename_i d hd
    simp only [Option.some.injEq] at h; subst h
    refine ⟨σ1.set "_" 0, h0.trans ?_⟩
    refine .step (c' := ⟨.call "_" .handoff [], k, σ1, l2⟩)
      (by simp [step, Expr.eval, BinOp.eval, σ1, l1, hd]; exact encC_some_ne _) ?_
    exact .single (by simp [step, mprims, l2, l1])
  · rename_i hd
    have hd' : (stOf l1).next c = none := hd
    have hn0 : σ1 "n" = 0 := by simp [σ1, hd', encC]
    let l3 := mpull ε c l2
    let kv : Val := if tailOf (stOf l3) = some c then 1 else 0
    let iteK : Stmt MPrim := .ite (.bin .eq (.var "k") (.const 0))
      (.seq (.call "n" .getNext []) (.seq loopN (.call "_" .handoff []))) .skip
    have h1 : Star (mprims ε c) ⟨.ite (.bin .ne (.var "n") (.const 0)) (.call "_" .handoff []) tail', k, σ1, l2⟩
        ⟨iteK, k, σ1.set "k" kv, ⟨c, .cas⟩ :: l3⟩ := by
      refine .step (c' := ⟨tail', k, σ1, l2⟩) (by simp [step, Expr.eval, BinOp.eval, hn0]) ?_
      refine .step (c' := ⟨.call "k" .cas [], .seq iteK k, σ1, l2⟩) (by simp [step, tail', iteK]) ?_
      refine .step (c' := ⟨.skip, .seq iteK k, σ1.set "k" kv, ⟨c, .cas⟩ :: l3⟩)
        (by simp [step, mprims, l3, kv]) ?_
      exact .single (by simp [step])
    split at h
    · rename_i ht
      have ht' : tailOf (stOf l3) = some c := ht
      simp only [Option.some.injEq] at h; subst h
      exact ⟨σ1.set "k" kv, h0.trans (h1.trans (.single (by simp [step, iteK, Expr.eval, BinOp.eval, kv, ht', l3, l2, l1])))⟩
    · rename_i ht
      have ht' : ¬ tailOf (stOf l3) = some c := ht
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨r0, hw, rfl⟩ := h
      let σk := σ1.set "k" kv
      let l5 := mpull ε c (⟨c, .cas⟩ :: l3)
      let σ5 := σk.set "n" (encC ((stOf l5).next c))
      obtain ⟨σ6, hloop⟩ := loopN_sim ε c fuel ((stOf l5).next c) σ5 (⟨c, .getNext⟩ :: l5) r0
        (.seq (.call "_" .handoff []) k) (by simp [σ5]) (by simpa [l5, l3, l2, l1] using hw)
      refine ⟨σ6.set "_" 0, h0.trans (h1.trans ?_)⟩
      refine .step (c' := ⟨.seq (.call "n" .getNext []) (.seq loopN (.call "_" .handoff [])), k, σk,
        ⟨c, .cas⟩ :: l3⟩) (by simp [step, iteK, Expr.eval, BinOp.eval, σk, kv, ht']) ?_
      refine .step (c' := ⟨.call "n" .getNext [], .seq (.seq loopN (.call "_" .handoff [])) k, σk,
        ⟨c, .cas⟩ :: l3⟩) (by simp [step]) ?_
      refine .step (c' := ⟨.skip, .seq (.seq loopN (.call "_" .handoff [])) k, σ5, ⟨c, .getNext⟩ :: l5⟩)
        (by simp [step, mprims, σ5, l5]) ?_
      refine .step (c' := ⟨.seq loopN (.call "_" .handoff []), k, σ5, ⟨c, .getNext⟩ :: l5⟩)
        (by simp [step]) ?_
      refine .step (c' := ⟨loopN, .seq (.call "_" .handoff []) k, σ5, ⟨c, .getNext⟩ :: l5⟩)
        (by simp [step]) ?_
      refine hloop.trans ?_
      refine .step (c' := ⟨.call "_" .handoff [], k, σ6, r0⟩) (by simp [step]) ?_
      exact .single (by simp [step, mprims])

/-! ## The same atomic interface as the ticket lock -/

theorem mreplay_hist_ext {l : MLog} {s : MS} {h : List HEvent} (hl : mreplay l = some (s, h)) :
    ∀ (xs : MLog) {s' : MS} {h' : List HEvent}, mreplay (xs ++ l) = some (s', h') → ∃ E, h' = E ++ h
  | [], s', h', hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨[], rfl⟩
  | e :: xs, s', h', hr => by
    obtain ⟨s2, h2, o, hl2, -, rfl⟩ := mreplay_cons hr
    obtain ⟨E, rfl⟩ := mreplay_hist_ext hl xs hl2
    exact ⟨consOpt o E, consOpt_append o E h⟩

theorem ext_mpull (ε : MEnv) (c : CPU) {r l : MLog} (h : ∃ xs, r = xs ++ l) : ∃ xs, mpull ε c r = xs ++ l := by
  obtain ⟨xs, rfl⟩ := h; exact ⟨ε.query c (xs ++ l) ++ xs, by simp [mpull]⟩

theorem ext_mcons (e : MEvent) {r l : MLog} (h : ∃ xs, r = xs ++ l) : ∃ xs, e :: r = xs ++ l := by
  obtain ⟨xs, rfl⟩ := h; exact ⟨e :: xs, rfl⟩

theorem waitB_ext (ε : MEnv) (c : CPU) :
    ∀ f b r r' l, waitB ε c f b r = some r' → (∃ xs, r = xs ++ l) → ∃ xs, r' = xs ++ l := by
  intro f
  induction f with
  | zero => intro b r r' l h hr; cases b <;> simp [waitB] at h; subst h; exact hr
  | succ f ih =>
    intro b r r' l h hr
    cases b
    · simp [waitB] at h; subst h; exact hr
    · simp only [waitB] at h; exact ih _ _ _ l h (ext_mcons _ (ext_mpull ε c hr))

theorem waitN_ext (ε : MEnv) (c : CPU) :
    ∀ f nx r r' l, waitN ε c f nx r = some r' → (∃ xs, r = xs ++ l) → ∃ xs, r' = xs ++ l := by
  intro f
  induction f with
  | zero => intro nx r r' l h hr; cases nx <;> simp [waitN] at h; subst h; exact hr
  | succ f ih =>
    intro nx r r' l h hr
    cases nx
    · simp only [waitN] at h; exact ih _ _ _ l h (ext_mcons _ (ext_mpull ε c hr))
    · simp [waitN] at h; subst h; exact hr

theorem acquireSpecM_ext {ε : MEnv} {c : CPU} {fuel : Nat} {l r : MLog}
    (h : acquireSpecM ε c fuel l = some r) : ∃ xs, r = xs ++ l := by
  have e0 : ∃ xs, l = xs ++ l := ⟨[], rfl⟩
  have e2 := ext_mcons ⟨c, .swap⟩ (ext_mpull ε c e0)
  simp only [acquireSpecM] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ext_mcons _ (ext_mpull ε c e2)
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨r0, hw, rfl⟩ := h
    have e4 := ext_mcons ⟨c, .getBusy⟩ (ext_mpull ε c (ext_mcons ⟨c, .link⟩ (ext_mpull ε c e2)))
    exact ext_mcons _ (ext_mpull ε c (waitB_ext ε c _ _ _ _ l hw e4))

theorem releaseSpecM_ext {ε : MEnv} {c : CPU} {fuel : Nat} {l r : MLog}
    (h : releaseSpecM ε c fuel l = some r) : ∃ xs, r = xs ++ l := by
  have e0 : ∃ xs, l = xs ++ l := ⟨[], rfl⟩
  have e2 := ext_mcons ⟨c, .getNext⟩ (ext_mpull ε c e0)
  simp only [releaseSpecM] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ext_mcons _ (ext_mpull ε c e2)
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact ext_mcons _ (ext_mpull ε c e2)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨r0, hw, rfl⟩ := h
      have e5 := ext_mcons ⟨c, .getNext⟩ (ext_mpull ε c (ext_mcons ⟨c, .cas⟩ (ext_mpull ε c e2)))
      exact ext_mcons _ (ext_mpull ε c (waitN_ext ε c _ _ _ _ l hw e5))

/-- Our new high-level events are only on top; everything else is others'. -/
theorem others_part {c : CPU} {E h : List HEvent} (hf : cpuF c (E ++ h) = cpuF c h) :
    ∀ e ∈ E, e.cpu ≠ c := by
  have hnil : cpuF c E = [] := by
    simp only [cpuF, List.filter_append] at hf
    have := congrArg List.length hf; simp only [List.length_append] at this
    simp only [cpuF]; exact List.eq_nil_of_length_eq_zero (by omega)
  intro e he hec
  have : e ∈ cpuF c E := by simp [cpuF, he, hec]
  rw [hnil] at this; simp at this

def RelLogM (l : MLog) (h : List HEvent) : Prop := ∃ s, mreplay l = some (s, h)

/-- **MCS `acquire` ⊑ the atomic `acq`** — the same L1 primitive the ticket
lock implements. -/
theorem acquireM_refines_atomic {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay l = some (s, h)) (hidle : s.ph c = .idle)
    (bound : MLog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K) (hF : FairB ε c bound) (loc : Locals) :
    ∃ (εH : HEnv) (loc' : Locals) (r : MLog) (h' : List HEvent),
      HRely εH c ∧ Star (mprims ε c) ⟨acquireM, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
      hprims εH c .acq [] h = some (0, h') ∧ RelLogM r h' := by
  obtain ⟨fuel, r, hspec⟩ := acquireM_live hc hR hl hidle bound K hK hF
  obtain ⟨loc', hstar⟩ := acquireM_sim ε c fuel loc l r .stop hspec
  obtain ⟨s', h₁, hr, -, hf⟩ := acquireM_guarantee hc hR hl hidle hspec
  obtain ⟨xs, rfl⟩ := acquireSpecM_ext hspec
  obtain ⟨E1, hE1⟩ := mreplay_hist_ext hl xs hr
  -- hE1 : acq c :: h₁ = E1 ++ h; peel our acq
  cases E1 with
  | nil =>
    exfalso
    simp only [List.nil_append] at hE1
    have h3 : cpuF c h = .acq c :: cpuF c h₁ := by rw [← hE1]; simp [cpuF, HEvent.cpu]
    rw [hf] at h3
    have := congrArg List.length h3; simp at this
  | cons a E =>
    simp only [List.cons_append, List.cons.injEq] at hE1
    obtain ⟨rfl, rfl⟩ := hE1
    have hE : ∀ e ∈ E, e.cpu ≠ c := others_part hf
    obtain ⟨o, ho, -⟩ := mreplay_hreplay hr
    have hfree : hreplay (E ++ h) = some none := hreplay_acq ho
    have hEt : ∀ p ∈ [(h, E)], ∀ e ∈ p.2, e.cpu ≠ c := fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact hE
    refine ⟨HEnv.table c [(h, E)] hEt, loc', _, .acq c :: (E ++ h), ?_, hstar,
      by simp [hprims, hpull_table, lookup, hfree], ⟨s', hr⟩⟩
    exact table_rely c _ _ (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨_, hfree⟩)

/-- **MCS `release` ⊑ the atomic `rel`**, which needs no environment: while
`c` holds the lock nobody else can add a high-level event. -/
theorem releaseM_refines_atomic {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {l : MLog} {s : MS}
    {h : List HEvent} (hl : mreplay l = some (s, h)) (hh : s.ph c = .holding)
    (bound : MLog → Nat) (hF : FairN ε c bound) (loc : Locals) :
    ∃ (loc' : Locals) (r : MLog),
      Star (mprims ε c) ⟨releaseM, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
      (∀ εH : HEnv, hprims εH c .rel [] h = some (0, .rel c :: h)) ∧ RelLogM r (.rel c :: h) := by
  obtain ⟨fuel, r, hspec⟩ := releaseM_live hc hR hl hh bound hF
  obtain ⟨loc', hstar⟩ := releaseM_sim ε c fuel loc l r .stop hspec
  obtain ⟨s', h₁, hr, -, hf⟩ := releaseM_guarantee hc hR hl hh hspec
  obtain ⟨xs, rfl⟩ := releaseSpecM_ext hspec
  obtain ⟨E1, hE1⟩ := mreplay_hist_ext hl xs hr
  obtain ⟨o0, ho0, hH0⟩ := mreplay_hreplay hl
  have hheld : hreplay h = some (some c) := by rw [ho0, (hH0 c).1 hh]
  cases E1 with
  | nil =>
    exfalso
    simp only [List.nil_append] at hE1
    have h3 : cpuF c h = .rel c :: cpuF c h₁ := by rw [← hE1]; simp [cpuF, HEvent.cpu]
    rw [hf] at h3
    have := congrArg List.length h3; simp at this
  | cons a E =>
    simp only [List.cons_append, List.cons.injEq] at hE1
    obtain ⟨rfl, rfl⟩ := hE1
    obtain ⟨o, ho, -⟩ := mreplay_hreplay hr
    have hE0 : E = [] := held_no_env hheld E (others_part hf) (hreplay_rel ho)
    subst hE0
    exact ⟨loc', _, hstar, fun εH => by simp [hprims, hheld], ⟨s', hr⟩⟩

end MCS
