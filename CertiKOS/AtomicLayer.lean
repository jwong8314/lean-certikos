import CertiKOS.TicketProtocol

/-!
# Layer L1: an atomic lock, and the refinement L0 (ticket lock in C) ⊑ L1

This is the CCAL step that the earlier files only approximated.

* **L1** is a separate layer. Its abstract state is the *high-level* log
  `HLog` (only `acq c` / `rel c` events). It has its own environment context
  `HEnv` (ε_H), which returns other CPUs' high-level events, and two atomic
  primitives:
  - `acq`: pull from ε_H; the lock must be free; append `acq c`.
  - `rel`: pull from ε_H; `c` must hold the lock; append `rel c`.
  `hreplay` tracks the single holder, so mutual exclusion is built into L1.
* **Refinement relation** `RelLog l h`: the low-level log `l` replays through
  the ticket protocol to the high-level log `h`.
* **ε_L ↦ ε_H** (`acquire_refines_atomic`, `release_refines_atomic`): for every
  low-level environment satisfying the protocol rely (and, for acquire, the
  fairness bound), we *construct* a high-level environment ε_H. Under that ε_H,
  the one-line L1 call `acq()` (or `rel()`) succeeds atomically and ends in a
  high-level log related to the final low-level log of the C code. ε_H only
  reports other CPUs' events and keeps the high-level log well formed (`HRely`).
  For acquire, the C code also cannot diverge.
* **Composition** (`critical_section_refines`): one ε_H serves a whole
  `acq(); rel()` critical section.

ε_H is built per run, as a finite table from high-level logs to the events
other CPUs produced while the C code ran. This mirrors the CCAL proof, where
ε_H is constructed from a fixed ε_L and the (deterministic) low-level run.
-/

namespace Ticket

open ClightL

/-! ## The layer interface L1 -/

abbrev HLog := List HEvent

/-- High-level environment context ε_H. -/
structure HEnv where
  query : CPU → HLog → List HEvent
  noSelf : ∀ c h e, e ∈ query c h → e.cpu ≠ c

def hpull (εH : HEnv) (c : CPU) (h : HLog) : HLog := εH.query c h ++ h

/-- Lock-holder transition of the atomic lock. -/
def hstep : Option CPU → HEvent → Option (Option CPU)
  | none, .acq c => some (some c)
  | some d, .rel c => if d = c then some none else none
  | _, _ => none

/-- Replay a high-level log to the current holder (`none` = free). -/
def hreplay : HLog → Option (Option CPU)
  | [] => some none
  | e :: h =>
    match hreplay h with
    | none => none
    | some o => hstep o e

inductive HPrim
  | acq | rel

/-- L1 primitives for CPU `c`: one atomic event each. As in CCAL's
`φ_acq[i]` / `φ_rel[i]`, `acq` queries the environment and `rel` does not,
because the CPU stays in the critical state until it releases. -/
def hprims (εH : HEnv) (c : CPU) : Prims HPrim HLog
  | .acq, [], h =>
      if hreplay (hpull εH c h) = some none then some (0, .acq c :: hpull εH c h) else none
  | .rel, [], h =>
      -- critical state (PLDI'18 §2): no query to ε_H while holding the lock
      if hreplay h = some (some c) then some (0, .rel c :: h) else none
  | _, _, _ => none

/-- High-level rely: other CPUs keep the high-level log well formed. -/
def HRely (εH : HEnv) (c : CPU) : Prop :=
  ∀ h o, hreplay h = some o → ∃ o', hreplay (hpull εH c h) = some o'

/-- The L1 client code: a single call. -/
def acqCodeH : Stmt HPrim := .call "_" .acq []
def relCodeH : Stmt HPrim := .call "_" .rel []

theorem hreplay_acq {c : CPU} {h : HLog} {o : Option CPU}
    (H : hreplay (.acq c :: h) = some o) : hreplay h = some none := by
  simp only [hreplay] at H
  split at H
  · simp at H
  · rename_i o₁ ho₁
    cases o₁ with
    | none => exact ho₁
    | some d => simp [hstep] at H

theorem hreplay_rel {c : CPU} {h : HLog} {o : Option CPU}
    (H : hreplay (.rel c :: h) = some o) : hreplay h = some (some c) := by
  simp only [hreplay] at H
  split at H
  · simp at H
  · rename_i o₁ ho₁
    cases o₁ with
    | none => simp [hstep] at H
    | some d =>
      simp only [hstep] at H
      split at H
      · rename_i hd; rw [ho₁, hd]
      · simp at H

/-! ## L0 replay agrees with L1 replay -/

/-- `o` names exactly the CPU that holds the lock in protocol state `s`. -/
def Holds (s : PState) (o : Option CPU) : Prop :=
  ∀ d, (∃ t, s.phase d = .holding t) ↔ o = some d

theorem replay_hreplay : ∀ {l : Log} {s : PState} {h : HLog},
    replay l = some (s, h) → ∃ o, hreplay h = some o ∧ Holds s o
  | [], s, h, hr => by
    simp [replay] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨none, rfl, fun d => by simp [PState.init]⟩
  | e :: l, s', h', hr => by
    obtain ⟨s, h, o, hl, hp, rfl⟩ := replay_cons hr
    obtain ⟨ho, hho, hH⟩ := replay_hreplay hl
    have hi := replay_inv hl
    obtain ⟨c, k⟩ := e
    simp only [pstep] at hp
    split at hp
    case isFalse => simp at hp
    cases k <;> cases hph : s.phase c <;> simp only [hph] at hp <;> try simp at hp
    · -- incTicket from idle: holder unchanged, no high-level event
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨ho, hho, fun d => ?_⟩
      by_cases hd : d = c
      · subst hd
        simp only [setPhase_same]
        constructor
        · rintro ⟨t, ht⟩; cases ht
        · intro h1; obtain ⟨t, ht⟩ := (hH _).2 h1; rw [hph] at ht; cases ht
      · simp only [setPhase_other _ _ hd]; exact hH d
    · -- getNow while waiting: a pure read
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨ho, by simpa [consOpt] using hho, hH⟩
    · -- incNow while holding
      rename_i t0
      obtain ⟨rfl, rfl⟩ := hp
      have hsome : ho = some c := (hH c).1 ⟨t0, hph⟩
      subst hsome
      refine ⟨none, by simp [consOpt, hreplay, hho, hstep], fun d => ?_⟩
      by_cases hd : d = c
      · subst hd; simp
      · simp only [setPhase_other _ _ hd]
        rw [hH d]; simp [Ne.symm hd]
    · -- hold while waiting: becomes `acq c`
      rename_i t0
      obtain ⟨heq, rfl, rfl⟩ := hp
      have hnone : ho = none := by
        cases ho with
        | none => rfl
        | some d =>
          obtain ⟨t, ht⟩ := (hH d).2 rfl
          have htn := hi.holdNow d t ht
          have hdc : d = c :=
            hi.uniq d c s.now (by simp [ht, Phase.tk, htn]) (by simp [hph, Phase.tk, heq])
          subst hdc; rw [hph] at ht; cases ht
      subst hnone
      refine ⟨some c, by simp [consOpt, hreplay, hho, hstep], fun d => ?_⟩
      by_cases hd : d = c
      · subst hd; simp
      · simp only [setPhase_other _ _ hd]
        rw [hH d]; simp [Ne.symm hd]

/-! ## Logs only grow; splitting off other CPUs' high-level events -/

theorem waitLoop_ext (ε : EnvCtx) (c : CPU) (t : Val) :
    ∀ f n l r, waitLoop ε c t f n l = some r → ∃ xs, r = xs ++ l := by
  intro f
  induction f with
  | zero =>
    intro n l r h
    by_cases hnt : n = t
    · simp [waitLoop, hnt] at h; exact ⟨[], by simp [h]⟩
    · simp [waitLoop, hnt] at h
  | succ f ih =>
    intro n l r h
    by_cases hnt : n = t
    · simp [waitLoop, hnt] at h; exact ⟨[], by simp [h]⟩
    · simp only [waitLoop, hnt, ite_false] at h
      obtain ⟨xs, rfl⟩ := ih _ _ _ h
      exact ⟨xs ++ ⟨c, .getNow⟩ :: ε.query c l, by simp [pull]⟩

theorem acquireSpec_ext {ε : EnvCtx} {c : CPU} {fuel : Nat} {l r : Log}
    (h : acquireSpec ε c fuel l = some r) : ∃ xs, r = xs ++ l := by
  obtain ⟨r0, hw, rfl⟩ := acquireSpec_some h
  obtain ⟨xs, rfl⟩ := waitLoop_ext ε c _ _ _ _ _ hw
  refine ⟨⟨c, .hold⟩ :: ε.query c (xs ++ (⟨c, .getNow⟩ :: pull ε c (⟨c, .incTicket⟩ :: pull ε c l)))
    ++ xs ++ [⟨c, .getNow⟩] ++ ε.query c (⟨c, .incTicket⟩ :: pull ε c l) ++ [⟨c, .incTicket⟩]
    ++ ε.query c l, ?_⟩
  simp [holdSpec, pull]

theorem consOpt_append (o : Option HEvent) (E h : List HEvent) :
    consOpt o (E ++ h) = consOpt o E ++ h := by cases o <;> rfl

theorem replay_hist_ext {l : Log} {s : PState} {h : HLog} (hl : replay l = some (s, h)) :
    ∀ (xs : Log) {s' : PState} {h' : HLog}, replay (xs ++ l) = some (s', h') → ∃ E, h' = E ++ h
  | [], s', h', hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨[], rfl⟩
  | e :: xs, s', h', hr => by
    rw [List.cons_append] at hr
    obtain ⟨s2, h2, o, hl2, _, rfl⟩ := replay_cons hr
    obtain ⟨E, rfl⟩ := replay_hist_ext hl xs hl2
    exact ⟨consOpt o E, consOpt_append o E h⟩

theorem cpuFilter_append (c : CPU) (a b : List HEvent) :
    cpuFilter c (a ++ b) = cpuFilter c a ++ cpuFilter c b := by
  simp [cpuFilter, List.filter_append]

/-- If a run of `c` extends the log, ends with `c`'s own event `x`, and adds
nothing else of `c`'s, then everything between is other CPUs' events. -/
theorem hist_split {c : CPU} {l : Log} {s : PState} {h : HLog} (hl : replay l = some (s, h))
    {xs : Log} {s' : PState} {x : HEvent} {h₁ : HLog}
    (hr : replay (xs ++ l) = some (s', x :: h₁)) (hx : x.cpu = c)
    (hf : cpuFilter c h₁ = cpuFilter c h) :
    ∃ E, h₁ = E ++ h ∧ ∀ e ∈ E, e.cpu ≠ c := by
  obtain ⟨E', hE'⟩ := replay_hist_ext hl xs hr
  cases E' with
  | nil =>
    simp only [List.nil_append] at hE'
    subst hE'
    have := congrArg List.length hf
    simp [cpuFilter, hx] at this
  | cons y E =>
    simp only [List.cons_append, List.cons.injEq] at hE'
    obtain ⟨-, rfl⟩ := hE'
    refine ⟨E, rfl, ?_⟩
    rw [cpuFilter_append] at hf
    have hnil : cpuFilter c E = [] := by
      have := congrArg List.length hf
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    intro e he hec
    have : e ∈ cpuFilter c E := by simp [cpuFilter, he, hec]
    rw [hnil] at this; simp at this

/-! ## Building ε_H: a finite table from high-level logs to others' events -/

def lookup (h : HLog) : List (HLog × List HEvent) → List HEvent
  | [] => []
  | p :: t => if h = p.1 then p.2 else lookup h t

theorem lookup_cases (h : HLog) : ∀ tbl : List (HLog × List HEvent),
    lookup h tbl = [] ∨ ∃ p ∈ tbl, p.1 = h ∧ lookup h tbl = p.2
  | [] => Or.inl rfl
  | p :: t => by
    by_cases hp : h = p.1
    · exact Or.inr ⟨p, List.mem_cons_self, hp.symm, by simp [lookup, hp]⟩
    · rcases lookup_cases h t with h1 | ⟨q, hq, h2, h3⟩
      · exact Or.inl (by simp [lookup, hp, h1])
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h2, by simp [lookup, hp, h3]⟩

def HEnv.table (c : CPU) (tbl : List (HLog × List HEvent))
    (hE : ∀ p ∈ tbl, ∀ e ∈ p.2, e.cpu ≠ c) : HEnv where
  query d h := if d = c then lookup h tbl else []
  noSelf := by
    intro d h e he
    by_cases hd : d = c
    · subst hd
      split at he
      case isFalse hne => exact absurd rfl hne
      rcases lookup_cases h tbl with h1 | ⟨p, hp, -, h3⟩
      · rw [h1] at he; simp at he
      · rw [h3] at he; exact hE p hp e he
    · simp [hd] at he

theorem hpull_table (c : CPU) (tbl : List (HLog × List HEvent)) (hE) (h : HLog) :
    hpull (HEnv.table c tbl hE) c h = lookup h tbl ++ h := by
  simp [hpull, HEnv.table]

theorem table_rely (c : CPU) (tbl : List (HLog × List HEvent)) (hE)
    (htbl : ∀ p ∈ tbl, ∃ o, hreplay (p.2 ++ p.1) = some o) : HRely (HEnv.table c tbl hE) c := by
  intro h o ho
  rw [hpull_table]
  rcases lookup_cases h tbl with h1 | ⟨p, hp, h2, h3⟩
  · rw [h1]; exact ⟨o, ho⟩
  · rw [h3]; subst h2; exact htbl p hp

/-! ## The refinement -/

/-- Refinement relation between the L0 log and the L1 log. -/
def RelLog (l : Log) (h : HLog) : Prop := ∃ s, replay l = some (s, h)

/-- **acquire (C on L0) ⊑ atomic `acq` (L1).** For every ε_L satisfying the
protocol rely and fairness, there is an ε_H (satisfying `HRely`) under which:
the C code reaches a final state and cannot diverge; the L1 primitive `acq`
succeeds in one step; and the two final logs are related. -/
theorem acquire_refines_atomic {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : HLog}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle)
    (bound : Log → Nat) (hF : FairP ε c (ticket (pull ε c l)) bound) (loc : Locals) :
    ∃ (εH : HEnv) (loc' : Locals) (r : Log) (h' : HLog),
      HRely εH c ∧
      Star (prims ε c) ⟨acquireCode, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
      ¬ Diverges (prims ε c) ⟨acquireCode, .stop, loc, l⟩ ∧
      hprims εH c .acq [] h = some (0, h') ∧
      Star (hprims εH c) ⟨acqCodeH, .stop, loc, h⟩ ⟨.skip, .stop, loc.set "_" 0, h'⟩ ∧
      RelLog r h' := by
  obtain ⟨fuel, r, hspec⟩ := acquire_live_proto hc hR hl hidle bound hF
  obtain ⟨loc', hstar⟩ := acquire_sim ε c fuel loc l r hspec
  obtain ⟨s', h₁, hr, -, hf⟩ := acquire_guarantee hc hR hl hidle hspec
  obtain ⟨xs, rfl⟩ := acquireSpec_ext hspec
  obtain ⟨E, rfl, hE⟩ := hist_split hl hr rfl hf
  obtain ⟨o, ho, -⟩ := replay_hreplay hr
  have hfree : hreplay (E ++ h) = some none := hreplay_acq ho
  have hEt : ∀ p ∈ [(h, E)], ∀ e ∈ p.2, e.cpu ≠ c := fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact hE
  have hprim : hprims (HEnv.table c [(h, E)] hEt) c .acq [] h = some (0, .acq c :: (E ++ h)) := by
    simp [hprims, hpull_table, lookup, hfree]
  refine ⟨HEnv.table c [(h, E)] hEt, loc', xs ++ l, .acq c :: (E ++ h), ?_, hstar,
    not_diverges_of_star_final hstar ⟨rfl, rfl⟩, hprim,
    Star.single (by simp [step, acqCodeH, hprim]), ⟨s', hr⟩⟩
  exact table_rely c _ _ (fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact ⟨_, hfree⟩)

/-- While `c` holds the lock, no other CPU can add a high-level event: the only
valid move is `c`'s own `rel`. This is why L1's `rel` need not query ε_H. -/
theorem held_no_env {c : CPU} {h : HLog} (hh : hreplay h = some (some c)) :
    ∀ (E : List HEvent) {o : Option CPU}, (∀ e ∈ E, e.cpu ≠ c) → hreplay (E ++ h) = some o → E = []
  | [], _, _, _ => rfl
  | e :: E, o, hE, hr => by
    exfalso
    simp only [List.cons_append, hreplay] at hr
    split at hr
    · simp at hr
    · rename_i o₁ ho₁
      have hE0 := held_no_env hh E (fun e' he' => hE e' (List.mem_cons_of_mem _ he')) ho₁
      subst hE0
      simp only [List.nil_append] at ho₁
      rw [hh] at ho₁; cases ho₁
      have hec := hE e List.mem_cons_self
      cases e with
      | acq d => simp [hstep] at hr
      | rel d =>
        simp only [hstep] at hr
        split at hr
        · rename_i hcd; exact hec (by simp [HEvent.cpu, hcd])
        · simp at hr

theorem hreplay_of_holding {l : Log} {s : PState} {h : HLog} {c : CPU} {t : Nat}
    (hl : replay l = some (s, h)) (hhold : s.phase c = .holding t) :
    hreplay h = some (some c) := by
  obtain ⟨o, ho, hH⟩ := replay_hreplay hl
  rw [ho, (hH c).1 ⟨t, hhold⟩]

/-- **release (C on L0) ⊑ atomic `rel` (L1).** In the critical state the L1
`rel` needs no environment at all: it succeeds for every ε_H. The L0 run may
see other CPUs' low-level events (spinning `get_n`, `FAI_t`), but none of them
is a high-level event, so the related L1 log is just `rel c :: h`. -/
theorem release_refines_atomic {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : HLog} {t : Nat}
    (hl : replay l = some (s, h)) (hhold : s.phase c = .holding t) (loc : Locals) :
    ∃ loc' : Locals,
      Star (prims ε c) ⟨releaseCode, .stop, loc, l⟩ ⟨.skip, .stop, loc', releaseSpec ε c l⟩ ∧
      (∀ εH : HEnv, hprims εH c .rel [] h = some (0, .rel c :: h) ∧
        Star (hprims εH c) ⟨relCodeH, .stop, loc, h⟩ ⟨.skip, .stop, loc.set "_" 0, .rel c :: h⟩) ∧
      RelLog (releaseSpec ε c l) (.rel c :: h) := by
  obtain ⟨loc', hstar⟩ := release_sim ε c loc l
  obtain ⟨s', h₁, hr, -, hf⟩ := release_guarantee hc hR hl hhold
  have hext : releaseSpec ε c l = (⟨c, .incNow⟩ :: ε.query c l) ++ l := by
    simp [releaseSpec, pull]
  rw [hext] at hr
  obtain ⟨E, rfl, hE⟩ := hist_split hl hr rfl hf
  obtain ⟨o, ho, -⟩ := replay_hreplay hr
  have hheld : hreplay h = some (some c) := hreplay_of_holding hl hhold
  have hE0 : E = [] := held_no_env hheld E hE (hreplay_rel ho)
  subst hE0
  have hprim : ∀ εH : HEnv, hprims εH c .rel [] h = some (0, .rel c :: h) := by
    intro εH; simp [hprims, hheld]
  refine ⟨loc', hstar, fun εH => ⟨hprim εH, Star.single (by simp [step, relCodeH, hprim])⟩,
    ⟨s', by rw [hext]; exact hr⟩⟩

/-- **A whole critical section.** One ε_H serves `acq(); rel()`: `acq` is
answered from a one-entry table, and `rel` asks nothing. -/
theorem critical_section_refines {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : HLog}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle)
    (bound : Log → Nat) (hF : FairP ε c (ticket (pull ε c l)) bound) :
    ∃ (fuel : Nat) (r : Log) (εH : HEnv) (h₁ : HLog),
      acquireSpec ε c fuel l = some r ∧
      HRely εH c ∧
      hprims εH c .acq [] h = some (0, h₁) ∧ RelLog r h₁ ∧
      hprims εH c .rel [] h₁ = some (0, .rel c :: h₁) ∧
      RelLog (releaseSpec ε c r) (.rel c :: h₁) := by
  obtain ⟨fuel, r, hspec⟩ := acquire_live_proto hc hR hl hidle bound hF
  obtain ⟨s', h₁, hr, hhold, hf⟩ := acquire_guarantee hc hR hl hidle hspec
  obtain ⟨xs, rfl⟩ := acquireSpec_ext hspec
  obtain ⟨E1, rfl, hE1⟩ := hist_split hl hr rfl hf
  obtain ⟨o1, ho1, -⟩ := replay_hreplay hr
  have hfree : hreplay (E1 ++ h) = some none := hreplay_acq ho1
  have hEt : ∀ p ∈ [(h, E1)], ∀ e ∈ p.2, e.cpu ≠ c := fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact hE1
  have hacq : hprims (HEnv.table c [(h, E1)] hEt) c .acq [] h =
      some (0, .acq c :: (E1 ++ h)) := by
    simp [hprims, hpull_table, lookup, hfree]
  obtain ⟨-, -, hrel, hrelLog⟩ := release_refines_atomic hc hR hr hhold (fun _ => 0)
  refine ⟨fuel, xs ++ l, HEnv.table c [(h, E1)] hEt, .acq c :: (E1 ++ h), hspec, ?_, hacq,
    ⟨s', hr⟩, (hrel _).1, hrelLog⟩
  exact table_rely c _ _ (fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact ⟨_, hfree⟩)

end Ticket
