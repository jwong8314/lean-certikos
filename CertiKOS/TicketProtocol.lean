import CertiKOS.TicketLock

/-!
# Ticket-lock protocol: mutual exclusion, linearization, and liveness over reachable states

This file adds the global, multi-CPU side of the CCAL argument for the ticket lock.

* **Protocol replay.** `replay` re-runs the shared log through a per-CPU protocol
  state machine (`idle → waiting t → holding t → idle`). It also produces the
  **high-level log**, as CCAL's relation R₁ does: `hold` becomes `acq c`, and
  `incNow` becomes `rel c`. `FAI_t` and `get_n` are invisible. A log that breaks
  the protocol does not replay (`none`).
* **Global invariant** (`Inv`) holds for every replayable log. It includes a
  counting fact, `ticket = now + #active CPUs`. With a fixed CPU count
  (`NCPU`, CertiKOS's `TOTAL_CPU`) this bounds `ticket - now`, which is exactly
  what makes the 32-bit `n != t` comparison safe against wraparound.
* **Mutual exclusion** (`mutex`): in any replayable log, at most one CPU holds the lock.
* **Guarantee / linearization** (`acquire_guarantee`): if the other CPUs follow
  the protocol (`RelyP`), then `acquire` started from `idle` ends in `holding`.
  Its *only* contribution to the high-level log is a single `acq c` at the very
  end. This is the per-CPU obligation behind "acquire is atomic".
* **Liveness over reachable states** (`acquire_live_proto`): the fairness
  assumption (`FairP`) only talks about replayable logs where we are waiting.
  "No overtaking" is no longer assumed: it follows from `Inv`.
* **End to end** (`acquire_correct`): the C code terminates, and its final log
  satisfies the guarantee.

* **Bounded liveness** (`acquire_live_bounded`): if the fairness measure is
  bounded by `K`, acquire returns within `(NCPU + 1) * (K + 1)` loop
  iterations, the analogue of CertiKOS's `n × m × k` (OSDI'16 Lemma 6).

The atomic layer is in `AtomicLayer.lean`, and a concrete fair scheduler in
`FairEnv.lean`.
-/

namespace Ticket

open ClightL

/-- Number of CPUs (CertiKOS `TOTAL_CPU`). -/
def NCPU : Nat := 8

inductive Phase
  | idle | waiting (t : Nat) | holding (t : Nat)
  deriving DecidableEq

def Phase.tk : Phase → Option Nat
  | .idle => none
  | .waiting t => some t
  | .holding t => some t

structure PState where
  ticket : Nat
  now : Nat
  phase : CPU → Phase

def setPhase (f : CPU → Phase) (c : CPU) (p : Phase) : CPU → Phase :=
  fun d => if d = c then p else f d

@[simp] theorem setPhase_same (f : CPU → Phase) (c : CPU) (p : Phase) :
    setPhase f c p c = p := by simp [setPhase]

theorem setPhase_other (f : CPU → Phase) {c d : CPU} (p : Phase) (h : d ≠ c) :
    setPhase f c p d = f d := by simp [setPhase, h]

/-- High-level (atomic lock) events. -/
inductive HEvent
  | acq (c : CPU) | rel (c : CPU)
  deriving DecidableEq

def HEvent.cpu : HEvent → CPU
  | .acq c => c
  | .rel c => c

/-- One protocol step. Returns the new state and the high-level event (if any).
As in CCAL's relation R₁ (PLDI'18 §2), `hold` becomes `acq`, `inc_n` becomes
`rel`, and the other lock events (`FAI_t`, `get_n`) are invisible. -/
def pstep (s : PState) (e : Event) : Option (PState × Option HEvent) :=
  if e.cpu < NCPU then
    match e.kind, s.phase e.cpu with
    | .incTicket, .idle =>
        some (⟨s.ticket + 1, s.now, setPhase s.phase e.cpu (.waiting s.ticket)⟩, none)
    | .getNow, .waiting _ => some (s, none)
    | .hold, .waiting t =>
        if s.now = t then
          some (⟨s.ticket, s.now, setPhase s.phase e.cpu (.holding t)⟩, some (.acq e.cpu))
        else none
    | .incNow, .holding _ =>
        some (⟨s.ticket, s.now + 1, setPhase s.phase e.cpu .idle⟩, some (.rel e.cpu))
    | _, _ => none
  else none

def PState.init : PState := ⟨0, 0, fun _ => .idle⟩

def consOpt (o : Option HEvent) (h : List HEvent) : List HEvent :=
  match o with
  | none => h
  | some he => he :: h

/-- Replay a log (newest first) from the initial state. Returns the protocol
state and the high-level log (newest first). -/
def replay : Log → Option (PState × List HEvent)
  | [] => some (PState.init, [])
  | e :: l =>
    match replay l with
    | none => none
    | some (s, h) =>
      match pstep s e with
      | none => none
      | some (s', o) => some (s', consOpt o h)

theorem replay_cons {e : Event} {l : Log} {s' : PState} {h' : List HEvent}
    (hr : replay (e :: l) = some (s', h')) :
    ∃ s h o, replay l = some (s, h) ∧ pstep s e = some (s', o) ∧ h' = consOpt o h := by
  simp only [replay] at hr
  split at hr
  · simp at hr
  · rename_i s h hl
    split at hr
    · simp at hr
    · rename_i s2 o hp
      simp at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨s, h, o, hl, hp, rfl⟩

theorem replay_cons_of {e : Event} {l : Log} {s s' : PState} {h : List HEvent}
    {o : Option HEvent} (hl : replay l = some (s, h)) (hp : pstep s e = some (s', o)) :
    replay (e :: l) = some (s', consOpt o h) := by
  simp [replay, hl, hp]

theorem replay_cons_some {e : Event} {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hp : (pstep s e).isSome) :
    ∃ s' h', replay ([e] ++ l) = some (s', h') := by
  cases hq : pstep s e with
  | none => simp [hq] at hp
  | some p =>
    obtain ⟨s', o⟩ := p
    exact ⟨s', consOpt o h, replay_cons_of hl hq⟩

/-! ## Counting active CPUs (no Mathlib, so a tiny counter) -/

def cnt (g : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt g n + (if g n then 1 else 0)

theorem cnt_le (g : Nat → Bool) : ∀ n, cnt g n ≤ n
  | 0 => by simp [cnt]
  | n + 1 => by have := cnt_le g n; simp only [cnt]; split <;> omega

theorem cnt_congr {g g' : Nat → Bool} : ∀ n, (∀ d, d < n → g d = g' d) → cnt g n = cnt g' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [cnt]
    rw [cnt_congr n (fun d hd => h d (by omega)), h n (by omega)]

theorem cnt_zero {g : Nat → Bool} (h : ∀ d, g d = false) : ∀ n, cnt g n = 0
  | 0 => rfl
  | n + 1 => by simp [cnt, cnt_zero h n, h]

theorem cnt_flip {g g' : Nat → Bool} (c : Nat) (hother : ∀ d, d ≠ c → g' d = g d)
    (hg : g c = false) (hg' : g' c = true) : ∀ n, c < n → cnt g' n = cnt g n + 1
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    simp only [cnt]
    by_cases hc : c = n
    · subst hc
      rw [cnt_congr c (fun d hd => hother d (by omega)), hg, hg']
      simp
    · rw [cnt_flip c hother hg hg' n (by omega), hother n (Ne.symm hc)]
      omega

def active (s : PState) : Nat := cnt (fun d => (s.phase d).tk.isSome) NCPU

/-! ## The global invariant -/

structure Inv (s : PState) : Prop where
  holdNow : ∀ c t, s.phase c = .holding t → t = s.now
  waitGe : ∀ c t, s.phase c = .waiting t → s.now ≤ t
  tkLt : ∀ c t, (s.phase c).tk = some t → t < s.ticket
  uniq : ∀ c d t, (s.phase c).tk = some t → (s.phase d).tk = some t → c = d
  idleOut : ∀ c, NCPU ≤ c → s.phase c = .idle
  count : s.ticket = s.now + active s

theorem inv_init : Inv PState.init where
  holdNow := by intro c t h; simp [PState.init] at h
  waitGe := by intro c t h; simp [PState.init] at h
  tkLt := by intro c t h; simp [PState.init, Phase.tk] at h
  uniq := by intro c d t h; simp [PState.init, Phase.tk] at h
  idleOut := by intro c _; rfl
  count := by
    simp only [PState.init, active]
    rw [cnt_zero (fun d => by simp [Phase.tk])]

/-- The active-CPU count bounds the number of outstanding tickets. -/
theorem Inv.outstanding_le {s : PState} (hi : Inv s) : s.ticket - s.now ≤ NCPU := by
  have := cnt_le (fun d => (s.phase d).tk.isSome) NCPU
  have := hi.count
  simp only [active] at *
  omega

theorem pstep_inv {s s' : PState} {e : Event} {o : Option HEvent}
    (hi : Inv s) (hp : pstep s e = some (s', o)) : Inv s' := by
  obtain ⟨c, k⟩ := e
  simp only [pstep] at hp
  split at hp
  case isFalse => simp at hp
  rename_i hc
  replace hc : c < NCPU := hc
  try simp only at hp hc
  cases k <;> cases hph : s.phase c <;> simp only [hph] at hp <;> try simp at hp
  · -- incTicket from idle
    obtain ⟨rfl, -⟩ := hp
    have hcnt : active ⟨s.ticket + 1, s.now, setPhase s.phase c (.waiting s.ticket)⟩
        = active s + 1 := by
      unfold active
      refine cnt_flip c (fun d hd => ?_) (by simp [hph, Phase.tk]) (by simp [Phase.tk]) NCPU hc
      simp [setPhase_other _ _ hd]
    constructor
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp at h
      · simp only [setPhase_other _ _ hd] at h; exact hi.holdNow d t h
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp at h; have := hi.count; simp only; omega
      · simp only [setPhase_other _ _ hd] at h; exact hi.waitGe d t h
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp [Phase.tk] at h; simp only; omega
      · simp only [setPhase_other _ _ hd] at h; have := hi.tkLt d t h; simp only; omega
    · intro d₁ d₂ t h₁ h₂
      by_cases e₁ : d₁ = c <;> by_cases e₂ : d₂ = c
      · rw [e₁, e₂]
      · subst e₁; simp only [setPhase_other _ _ e₂] at h₂; simp [Phase.tk] at h₁
        have := hi.tkLt d₂ t h₂; omega
      · subst e₂; simp only [setPhase_other _ _ e₁] at h₁; simp [Phase.tk] at h₂
        have := hi.tkLt d₁ t h₁; omega
      · simp only [setPhase_other _ _ e₁] at h₁; simp only [setPhase_other _ _ e₂] at h₂
        exact hi.uniq d₁ d₂ t h₁ h₂
    · intro d hd
      have : d ≠ c := Nat.ne_of_gt (Nat.lt_of_lt_of_le hc hd)
      simp only [setPhase_other _ _ this]; exact hi.idleOut d hd
    · rw [hcnt]; have := hi.count; simp only; omega
  · -- getNow while waiting: a pure read
    obtain ⟨rfl, -⟩ := hp; exact hi
  · -- incNow while holding
    rename_i t0
    obtain ⟨rfl, -⟩ := hp
    have ht0 : t0 = s.now := hi.holdNow c t0 hph
    have hcnt : active s = active ⟨s.ticket, s.now + 1, setPhase s.phase c .idle⟩ + 1 := by
      unfold active
      refine cnt_flip c (fun d hd => ?_) (by simp [Phase.tk]) (by simp [hph, Phase.tk]) NCPU hc
      simp [setPhase_other _ _ hd]
    have hne : ∀ d, d ≠ c → (s.phase d).tk ≠ some s.now := by
      intro d hd h
      exact hd (hi.uniq d c s.now h (by simp [hph, Phase.tk, ht0]))
    constructor
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp at h
      · simp only [setPhase_other _ _ hd] at h
        have := hi.holdNow d t h
        exact absurd (by simp [h, Phase.tk, this]) (hne d hd)
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp at h
      · simp only [setPhase_other _ _ hd] at h
        have h1 := hi.waitGe d t h
        have h2 : t ≠ s.now := fun heq => hne d hd (by simp [h, Phase.tk, heq])
        simp only; omega
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp [Phase.tk] at h
      · simp only [setPhase_other _ _ hd] at h; exact hi.tkLt d t h
    · intro d₁ d₂ t h₁ h₂
      by_cases e₁ : d₁ = c
      · subst e₁; simp [Phase.tk] at h₁
      by_cases e₂ : d₂ = c
      · subst e₂; simp [Phase.tk] at h₂
      simp only [setPhase_other _ _ e₁] at h₁; simp only [setPhase_other _ _ e₂] at h₂
      exact hi.uniq d₁ d₂ t h₁ h₂
    · intro d hd
      have : d ≠ c := Nat.ne_of_gt (Nat.lt_of_lt_of_le hc hd)
      simp only [setPhase_other _ _ this]; exact hi.idleOut d hd
    · have := hi.count
      have := hi.tkLt c t0 (by simp [hph, Phase.tk])
      simp only; omega
  · -- hold while waiting: the linearization point
    rename_i t0
    obtain ⟨heq, rfl, -⟩ := hp
    have htk : ∀ d, (setPhase s.phase c (.holding t0) d).tk = (s.phase d).tk := by
      intro d; by_cases hd : d = c
      · subst hd; simp [hph, Phase.tk]
      · rw [setPhase_other _ _ hd]
    have hcnt : active ⟨s.ticket, s.now, setPhase s.phase c (.holding t0)⟩ = active s := by
      unfold active; exact cnt_congr NCPU (fun d _ => by simp only [htk])
    constructor
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp at h; simp only; omega
      · simp only [setPhase_other _ _ hd] at h; exact hi.holdNow d t h
    · intro d t h
      by_cases hd : d = c
      · subst hd; simp at h
      · simp only [setPhase_other _ _ hd] at h; exact hi.waitGe d t h
    · intro d t h; rw [htk] at h; exact hi.tkLt d t h
    · intro d₁ d₂ t h₁ h₂; rw [htk] at h₁ h₂; exact hi.uniq d₁ d₂ t h₁ h₂
    · intro d hd
      have : d ≠ c := Nat.ne_of_gt (Nat.lt_of_lt_of_le hc hd)
      simp only [setPhase_other _ _ this]; exact hi.idleOut d hd
    · rw [hcnt]; exact hi.count

theorem replay_inv : ∀ {l : Log} {s : PState} {h : List HEvent},
    replay l = some (s, h) → Inv s
  | [], s, h, hr => by simp [replay] at hr; obtain ⟨rfl, -⟩ := hr; exact inv_init
  | _ :: _, _, _, hr => by
    obtain ⟨s0, h0, o, hl, hp, -⟩ := replay_cons hr
    exact pstep_inv (replay_inv hl) hp

/-- **Mutual exclusion**: in any protocol-conforming log, at most one CPU holds the lock. -/
theorem mutex {l : Log} {s : PState} {h : List HEvent} (hr : replay l = some (s, h))
    {c d : CPU} {t u : Nat} (hc : s.phase c = .holding t) (hd : s.phase d = .holding u) :
    c = d := by
  have hi := replay_inv hr
  have ht := hi.holdNow c t hc
  have hu := hi.holdNow d u hd
  exact hi.uniq c d s.now (by simp [hc, Phase.tk, ht]) (by simp [hd, Phase.tk, hu])

/-! ## Replay agrees with the counters; other CPUs' events don't touch us -/

theorem replay_counts : ∀ {l : Log} {s : PState} {h : List HEvent},
    replay l = some (s, h) → s.now = now l ∧ s.ticket = ticket l
  | [], s, h, hr => by
    simp [replay] at hr; obtain ⟨rfl, -⟩ := hr; simp [PState.init, now, ticket, countK]
  | e :: l, s', h', hr => by
    obtain ⟨s, h, o, hl, hp, -⟩ := replay_cons hr
    obtain ⟨ih1, ih2⟩ := replay_counts hl
    obtain ⟨c, k⟩ := e
    simp only [pstep] at hp
    split at hp
    case isFalse => simp at hp
    cases k <;> cases hph : s.phase c <;> simp only [hph] at hp <;> try simp at hp
    · obtain ⟨rfl, -⟩ := hp; simp [now, ticket, countK] at *; omega
    · obtain ⟨rfl, -⟩ := hp; simp [now, ticket, countK] at *; omega
    · obtain ⟨rfl, -⟩ := hp; simp [now, ticket, countK] at *; omega
    · obtain ⟨_, rfl, -⟩ := hp; simp [now, ticket, countK] at *; omega

def cpuFilter (c : CPU) (h : List HEvent) : List HEvent := h.filter (fun he => decide (he.cpu = c))

theorem pstep_other {s s' : PState} {e : Event} {o : Option HEvent} {c : CPU}
    (hp : pstep s e = some (s', o)) (hne : e.cpu ≠ c) :
    s'.phase c = s.phase c ∧ cpuFilter c (consOpt o []) = [] := by
  obtain ⟨d, k⟩ := e
  try simp only at hne
  simp only [pstep] at hp
  split at hp
  case isFalse => simp at hp
  have hcd : c ≠ d := Ne.symm hne
  cases k <;> cases hph : s.phase d <;> simp only [hph] at hp <;> try simp at hp
  · obtain ⟨rfl, rfl⟩ := hp; exact ⟨setPhase_other _ _ hcd, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hp
    exact ⟨setPhase_other _ _ hcd, by simp [cpuFilter, consOpt, HEvent.cpu, hne]⟩
  · obtain ⟨_, rfl, rfl⟩ := hp
    exact ⟨setPhase_other _ _ hcd, by simp [cpuFilter, consOpt, HEvent.cpu, hne]⟩

theorem cpuFilter_consOpt (c : CPU) (o : Option HEvent) (h : List HEvent)
    (ho : cpuFilter c (consOpt o []) = []) : cpuFilter c (consOpt o h) = cpuFilter c h := by
  cases o with
  | none => rfl
  | some he =>
    simp only [cpuFilter, consOpt, List.filter_cons] at ho ⊢
    split at ho <;> simp_all

/-- Events from other CPUs leave our phase and our high-level history unchanged. -/
theorem replay_others {c : CPU} : ∀ (xs : Log) {l : Log} {s s' : PState} {h h' : List HEvent},
    (∀ e ∈ xs, e.cpu ≠ c) → replay l = some (s, h) → replay (xs ++ l) = some (s', h') →
    s'.phase c = s.phase c ∧ cpuFilter c h' = cpuFilter c h
  | [], l, s, s', h, h', _, hl, hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨rfl, rfl⟩
  | e :: xs, l, s, s', h, h', hx, hl, hr => by
    obtain ⟨s2, h2, o, hl2, hp, rfl⟩ := replay_cons hr
    obtain ⟨ih1, ih2⟩ := replay_others xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2
    obtain ⟨hp1, hp2⟩ := pstep_other hp (hx e (List.mem_cons_self))
    exact ⟨hp1.trans ih1, (cpuFilter_consOpt c o h2 hp2).trans ih2⟩

/-! ## Rely and fairness, stated over reachable (replayable) logs only -/

/-- Rely: the other CPUs follow the ticket-lock protocol. -/
structure RelyP (ε : EnvCtx) (c : CPU) : Prop where
  conform : ∀ l s h, replay l = some (s, h) → ∃ s' h', replay (pull ε c l) = some (s', h')

/-- Fairness (`CalBound` style), only for reachable logs in which `c` waits for `tn`. -/
def FairP (ε : EnvCtx) (c : CPU) (tn : Nat) (bound : Log → Nat) : Prop :=
  ∀ l s h, replay l = some (s, h) → s.phase c = .waiting tn → s.now < tn →
    now l < now (pull ε c l) ∨ bound (⟨c, .getNow⟩ :: pull ε c l) < bound l

theorem pull_others {ε : EnvCtx} {c : CPU} (hR : RelyP ε c) {l : Log} {s : PState}
    {h : List HEvent} (hl : replay l = some (s, h)) :
    ∃ s' h', replay (pull ε c l) = some (s', h') ∧ s'.phase c = s.phase c ∧
      cpuFilter c h' = cpuFilter c h := by
  obtain ⟨s', h', hr⟩ := hR.conform l s h hl
  obtain ⟨h1, h2⟩ := replay_others (ε.query c l) (fun e he => ε.noSelf c l e he) hl hr
  exact ⟨s', h', hr, h1, h2⟩

/-! ## The wait-loop invariant -/

section Loop
variable (ε : EnvCtx) (c : CPU) (tn : Nat) (h₀ : List HEvent)

/-- State of the wait loop, observed right after a `get_n`: `c` still waits
for ticket `tn` and has produced no new high-level event. -/
def LoopInv (l : Log) : Prop :=
  ∃ s h, replay l = some (s, h) ∧ s.phase c = .waiting tn ∧ cpuFilter c h = cpuFilter c h₀

/-- After `hold`: `c` holds the lock, and its only new high-level event is
the `acq c` on top. -/
def AcqPost (l : Log) : Prop :=
  ∃ s h₁, replay l = some (s, .acq c :: h₁) ∧ s.phase c = .holding tn ∧
    cpuFilter c h₁ = cpuFilter c h₀

theorem after_getNow (hc : c < NCPU) (hR : RelyP ε c) {l : Log} (hi : LoopInv c tn h₀ l) :
    LoopInv c tn h₀ (⟨c, .getNow⟩ :: pull ε c l) := by
  obtain ⟨s, h, hl, hw, hf⟩ := hi
  obtain ⟨s1, h1, hr1, hph1, hf1⟩ := pull_others hR hl
  rw [hw] at hph1
  have hp : pstep s1 ⟨c, .getNow⟩ = some (s1, none) := by simp [pstep, hc, hph1]
  exact ⟨_, _, replay_cons_of hr1 hp, hph1, hf1.trans hf⟩

/-- The 32-bit comparison is exact for outstanding tickets. -/
theorem ofNat_eq_of_close {a b : Nat} (hab : a ≤ b) (hd : b - a < 2 ^ 32)
    (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- While waiting, `tn - now` is below `NCPU`; this is what keeps the 32-bit
test `n != t` exact (the bug CertiKOS found in `while (now < t)`). -/
theorem loopInv_gap {l : Log} (hi : LoopInv c tn h₀ l) : now l ≤ tn ∧ tn - now l < NCPU := by
  obtain ⟨s, h, hr, hph, _⟩ := hi
  have inv := replay_inv hr
  obtain ⟨hn, _⟩ := replay_counts hr
  have hle : s.now ≤ tn := inv.waitGe c tn hph
  have hlt : tn < s.ticket := inv.tkLt c tn (by simp [hph, Phase.tk])
  have hout := inv.outstanding_le
  omega

theorem loopInv_exit {l : Log} (hi : LoopInv c tn h₀ l)
    (heq : BitVec.ofNat 32 (now l) = BitVec.ofNat 32 tn) : now l = tn := by
  obtain ⟨h1, h2⟩ := loopInv_gap c tn h₀ hi
  exact ofNat_eq_of_close h1 (by simp only [NCPU] at h2; omega) heq

/-- `hold()` after the loop exits: `now` cannot move (nobody else can hold),
so `hold` is valid and produces exactly `acq c`. -/
theorem hold_post (hc : c < NCPU) (hR : RelyP ε c) {l : Log} (hi : LoopInv c tn h₀ l)
    (hn : now l = tn) : AcqPost c tn h₀ (holdSpec ε c l) := by
  obtain ⟨s, h, hl, hw, hf⟩ := hi
  obtain ⟨s1, h1, hr1, hph1, hf1⟩ := pull_others hR hl
  rw [hw] at hph1
  have inv1 := replay_inv hr1
  obtain ⟨hn1, -⟩ := replay_counts hr1
  have hge := now_pull_ge ε c l
  have hle := inv1.waitGe c tn hph1
  have heq : s1.now = tn := by omega
  have hp : pstep s1 ⟨c, .hold⟩ =
      some (⟨s1.ticket, s1.now, setPhase s1.phase c (.holding tn)⟩, some (.acq c)) := by
    simp [pstep, hc, hph1, heq]
  exact ⟨_, h1, replay_cons_of hr1 hp, by simp [heq], hf1.trans hf⟩

theorem loop_guarantee (hc : c < NCPU) (hR : RelyP ε c) :
    ∀ fuel l r, LoopInv c tn h₀ l →
      waitLoop ε c (BitVec.ofNat 32 tn) fuel (BitVec.ofNat 32 (now l)) l = some r →
      LoopInv c tn h₀ r ∧ now r = tn := by
  intro fuel
  induction fuel with
  | zero =>
    intro l r hi hw
    by_cases heq : BitVec.ofNat 32 (now l) = BitVec.ofNat 32 tn
    · simp [waitLoop, heq] at hw; subst hw; exact ⟨hi, loopInv_exit c tn h₀ hi heq⟩
    · simp [waitLoop, heq] at hw
  | succ f ih =>
    intro l r hi hw
    by_cases heq : BitVec.ofNat 32 (now l) = BitVec.ofNat 32 tn
    · simp [waitLoop, heq] at hw; subst hw; exact ⟨hi, loopInv_exit c tn h₀ hi heq⟩
    · simp only [waitLoop, heq, ite_false] at hw
      exact ih _ r (after_getNow ε c tn h₀ hc hR hi) (by simpa using hw)

theorem loop_live (hc : c < NCPU) (hR : RelyP ε c) (bound : Log → Nat)
    (hF : FairP ε c tn bound) :
    ∀ m b l, tn - now l = m → bound l = b → LoopInv c tn h₀ l →
      ∃ f r, waitLoop ε c (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now l)) l = some r := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro b
  induction b using Nat.strongRecOn with
  | _ b ihb =>
  intro l hm hb hi
  by_cases heq : BitVec.ofNat 32 (now l) = BitVec.ofNat 32 tn
  · exact ⟨0, l, by simp [waitLoop, heq]⟩
  · obtain ⟨s, h, hr, hph, hf⟩ := hi
    have inv := replay_inv hr
    obtain ⟨hsn, _⟩ := replay_counts hr
    have hne : now l ≠ tn := fun h => heq (by rw [h])
    have hlt : now l < tn := by have := inv.waitGe c tn hph; omega
    let l' : Log := ⟨c, .getNow⟩ :: pull ε c l
    have hi' : LoopInv c tn h₀ l' := after_getNow ε c tn h₀ hc hR ⟨s, h, hr, hph, hf⟩
    have hge : now l ≤ now l' := by simp [l']; exact now_pull_ge ε c l
    have step_eq : ∀ f, waitLoop ε c (BitVec.ofNat 32 tn) (f + 1) (BitVec.ofNat 32 (now l)) l
        = waitLoop ε c (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now l')) l' := by
      intro f; simp [waitLoop, heq, l']
    have hfair := hF l s h hr hph (by omega)
    rcases Nat.lt_or_eq_of_le hge with hgt | hEq
    · obtain ⟨f, r, hw⟩ := ihm (tn - now l') (by omega) (bound l') l' rfl rfl hi'
      exact ⟨f + 1, r, by rw [step_eq]; exact hw⟩
    · have hb' : bound l' < b := by
        rcases hfair with h1 | h1
        · simp [l'] at hEq; omega
        · rw [← hb]; exact h1
      obtain ⟨f, r, hw⟩ := ihb (bound l') hb' l' (by omega) rfl hi'
      exact ⟨f + 1, r, by rw [step_eq]; exact hw⟩

/-- **Explicit iteration bound** (the analogue of CertiKOS's `n × m × k`,
OSDI'16 Lemma 6). If the fairness counter never exceeds `K`, the loop needs at
most `(tn - now) * (K + 1) + bound` iterations. -/
theorem loop_live_bounded (hc : c < NCPU) (hR : RelyP ε c) (bound : Log → Nat) (K : Nat)
    (hK : ∀ l, bound l ≤ K) (hF : FairP ε c tn bound) :
    ∀ m b l, tn - now l = m → bound l = b → LoopInv c tn h₀ l →
      ∃ f r, f ≤ m * (K + 1) + b ∧
        waitLoop ε c (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now l)) l = some r := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro b
  induction b using Nat.strongRecOn with
  | _ b ihb =>
  intro l hm hb hi
  by_cases heq : BitVec.ofNat 32 (now l) = BitVec.ofNat 32 tn
  · exact ⟨0, l, Nat.zero_le _, by simp [waitLoop, heq]⟩
  · obtain ⟨s, h, hr, hph, hf⟩ := hi
    have inv := replay_inv hr
    obtain ⟨hsn, _⟩ := replay_counts hr
    have hne : now l ≠ tn := fun h => heq (by rw [h])
    have hlt : now l < tn := by have := inv.waitGe c tn hph; omega
    let l' : Log := ⟨c, .getNow⟩ :: pull ε c l
    have hi' : LoopInv c tn h₀ l' := after_getNow ε c tn h₀ hc hR ⟨s, h, hr, hph, hf⟩
    have hge : now l ≤ now l' := by simp [l']; exact now_pull_ge ε c l
    have step_eq : ∀ f, waitLoop ε c (BitVec.ofNat 32 tn) (f + 1) (BitVec.ofNat 32 (now l)) l
        = waitLoop ε c (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now l')) l' := by
      intro f; simp [waitLoop, heq, l']
    have hfair := hF l s h hr hph (by omega)
    rcases Nat.lt_or_eq_of_le hge with hgt | hEq
    · obtain ⟨f, r, hfle, hw⟩ := ihm (tn - now l') (by omega) (bound l') l' rfl rfl hi'
      have hm' : tn - now l' + 1 ≤ m := by omega
      have h1 := Nat.mul_le_mul_right (K + 1) hm'
      rw [Nat.succ_mul] at h1
      have h2 := hK l'
      exact ⟨f + 1, r, by omega, by rw [step_eq]; exact hw⟩
    · have hb' : bound l' < b := by
        rcases hfair with h1 | h1
        · simp [l'] at hEq; omega
        · rw [← hb]; exact h1
      obtain ⟨f, r, hfle, hw⟩ := ihb (bound l') hb' l' (by omega) rfl hi'
      exact ⟨f + 1, r, by omega, by rw [step_eq]; exact hw⟩

end Loop

theorem waitLoop_mono_le (ε : EnvCtx) (c : CPU) (t : Val) {f f' : Nat} {n : Val} {l r : Log}
    (hle : f ≤ f') (h : waitLoop ε c t f n l = some r) : waitLoop ε c t f' n l = some r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => exact waitLoop_mono ε c t _ _ _ _ ih

/-! ## `acquire`: guarantee, liveness, and the end-to-end statement -/

/-- The loop invariant holds right after the first `get_n` of `acquire`. -/
theorem acquire_enter {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle) :
    LoopInv c (ticket (pull ε c l)) h
      (⟨c, .getNow⟩ :: pull ε c (⟨c, .incTicket⟩ :: pull ε c l)) := by
  obtain ⟨s1, h1, hr1, hph1, hf1⟩ := pull_others hR hl
  obtain ⟨_, ht1⟩ := replay_counts hr1
  rw [hidle] at hph1
  have hp : pstep s1 ⟨c, .incTicket⟩ =
      some (⟨s1.ticket + 1, s1.now, setPhase s1.phase c (.waiting s1.ticket)⟩, none) := by
    simp [pstep, hc, hph1]
  have hr2 := replay_cons_of hr1 hp
  refine after_getNow ε c _ h hc hR ⟨_, _, hr2, by simp [ht1], ?_⟩
  simpa [consOpt] using hf1

/-- **Guarantee / linearization point.** Started from `idle`, whenever the spec
returns, the CPU ends up `holding`, and its only new high-level event is one
`acq c`, produced by `hold` at the very end. -/
theorem acquire_guarantee {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle)
    {fuel : Nat} {r : Log} (hspec : acquireSpec ε c fuel l = some r) :
    AcqPost c (ticket (pull ε c l)) h r := by
  obtain ⟨r0, hw, rfl⟩ := acquireSpec_some hspec
  have hi := acquire_enter hc hR hl hidle
  obtain ⟨hi', hn⟩ := loop_guarantee ε c _ h hc hR fuel _ r0 hi (by simpa using hw)
  exact hold_post ε c _ h hc hR hi' hn

/-- **Liveness** under the protocol rely and fairness over reachable logs only. -/
theorem acquire_live_proto {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle)
    (bound : Log → Nat) (hF : FairP ε c (ticket (pull ε c l)) bound) :
    ∃ fuel r, acquireSpec ε c fuel l = some r := by
  have hi := acquire_enter hc hR hl hidle
  obtain ⟨f, r, hw⟩ := loop_live ε c _ h hc hR bound hF _ _ _ rfl rfl hi
  exact ⟨f, _, acquireSpec_of_wait (by simpa using hw)⟩

/-- **Bounded liveness**: with a fairness counter bounded by `K`, the spec
returns within `(NCPU + 1) * (K + 1)` loop iterations. -/
theorem acquire_live_bounded {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle)
    (bound : Log → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : FairP ε c (ticket (pull ε c l)) bound) :
    ∃ r, acquireSpec ε c ((NCPU + 1) * (K + 1)) l = some r := by
  have hi := acquire_enter hc hR hl hidle
  obtain ⟨hgap1, hgap2⟩ := loopInv_gap c _ h hi
  obtain ⟨f, r, hfle, hw⟩ := loop_live_bounded ε c _ h hc hR bound K hK hF _ _ _ rfl rfl hi
  have h1 := Nat.mul_le_mul_right (K + 1) (Nat.le_of_lt hgap2)
  have h2 : (NCPU + 1) * (K + 1) = NCPU * (K + 1) + (K + 1) := Nat.succ_mul _ _
  have h3 := hK (⟨c, .getNow⟩ :: pull ε c (⟨c, .incTicket⟩ :: pull ε c l))
  have hle : f ≤ (NCPU + 1) * (K + 1) := by omega
  exact ⟨_, acquireSpec_of_wait (waitLoop_mono_le ε c _ hle (by simpa using hw))⟩

/-- **End to end** for the C code: under rely + fairness, `acquire` (ClightL)
reaches a final state; that is its only possible outcome (no divergence); and
the final log satisfies the guarantee. -/
theorem acquire_correct {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle)
    (bound : Log → Nat) (hF : FairP ε c (ticket (pull ε c l)) bound) (loc : Locals) :
    (∃ loc' r, Star (prims ε c) ⟨acquireCode, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
        AcqPost c (ticket (pull ε c l)) h r) ∧
      ¬ Diverges (prims ε c) ⟨acquireCode, .stop, loc, l⟩ := by
  obtain ⟨fuel, r, hspec⟩ := acquire_live_proto hc hR hl hidle bound hF
  obtain ⟨loc', hstar⟩ := acquire_sim ε c fuel loc l r hspec
  exact ⟨⟨loc', r, hstar, acquire_guarantee hc hR hl hidle hspec⟩,
    not_diverges_of_star_final hstar ⟨rfl, rfl⟩⟩

/-- `release` from `holding`: back to `idle`, contributing exactly one `rel c`. -/
theorem release_guarantee {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hR : RelyP ε c)
    {l : Log} {s : PState} {h : List HEvent} {t : Nat}
    (hl : replay l = some (s, h)) (hhold : s.phase c = .holding t) :
    ∃ s' h₁, replay (releaseSpec ε c l) = some (s', .rel c :: h₁) ∧
      s'.phase c = .idle ∧ cpuFilter c h₁ = cpuFilter c h := by
  obtain ⟨s1, h1, hr1, hph1, hf1⟩ := pull_others hR hl
  rw [hhold] at hph1
  have hp : pstep s1 ⟨c, .incNow⟩ =
      some (⟨s1.ticket, s1.now + 1, setPhase s1.phase c .idle⟩, some (.rel c)) := by
    simp [pstep, hc, hph1]
  exact ⟨_, h1, replay_cons_of hr1 hp, by simp, hf1⟩

/-! ## Non-vacuity: an environment that follows the protocol -/

/-- CPU 1 runs the protocol on its own: it takes a ticket when idle, polls when
waiting, and releases when holding. (CPU 1 itself sees no other events.) -/
def protoEnv : EnvCtx where
  query c l :=
    if c = 1 then []
    else match replay l with
      | some (s, _) =>
        match s.phase 1 with
        | .idle => [⟨1, .incTicket⟩]
        | .waiting t => if s.now = t then [⟨1, .hold⟩] else [⟨1, .getNow⟩]
        | .holding _ => [⟨1, .incNow⟩]
      | none => []
  noSelf := by
    intro c l e he
    by_cases h1 : c = 1
    · simp [h1] at he
    · simp only [h1, ite_false] at he
      split at he
      · split at he
        · simp at he; subst he; exact Ne.symm h1
        · split at he <;> simp at he <;> subst he <;> exact Ne.symm h1
        · simp at he; subst he; exact Ne.symm h1
      · simp at he

theorem protoEnv_rely (c : CPU) : RelyP protoEnv c where
  conform := by
    intro l s h hl
    by_cases h1 : c = 1
    · exact ⟨s, h, by simp [pull, protoEnv, h1, hl]⟩
    · have hlt : (1 : Nat) < NCPU := by decide
      simp only [pull, protoEnv, h1, ite_false, hl]
      cases hph : s.phase 1 with
      | idle =>
        exact replay_cons_some hl (by simp [pstep, hlt, hph])
      | waiting t =>
        by_cases heq : s.now = t
        · simp only [heq, ite_true]; exact replay_cons_some hl (by simp [pstep, hlt, hph, heq])
        · simp only [heq, ite_false]; exact replay_cons_some hl (by simp [pstep, hlt, hph])
      | holding t =>
        exact replay_cons_some hl (by simp [pstep, hlt, hph])

/-- CPU 1 currently holds the lock (ticket 0); CPU 0 is idle. -/
def heldLog : Log := [⟨1, .hold⟩, ⟨1, .getNow⟩, ⟨1, .incTicket⟩]

/-- A concrete run: under `protoEnv`, CPU 0's `acquire` from `heldLog`
returns within 3 iterations (CPU 1 releases, then CPU 0 gets the lock),
checked by evaluation. -/
theorem demo_proto_acquire : (acquireSpec protoEnv 0 3 heldLog).isSome = true := by
  decide

theorem demo_proto_guarantee {r : Log} (hspec : acquireSpec protoEnv 0 3 heldLog = some r) :
    AcqPost 0 (ticket (pull protoEnv 0 heldLog)) [.acq 1] r := by
  obtain ⟨s, hl, hidle⟩ : ∃ s, replay heldLog = some (s, [.acq 1]) ∧ s.phase 0 = .idle :=
    ⟨_, rfl, rfl⟩
  exact acquire_guarantee (by decide) (protoEnv_rely 0) hl hidle hspec

end Ticket
