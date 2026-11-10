import CertiKOS.AtomicLayer

/-!
# A concrete fair scheduler: the fairness hypothesis is satisfiable

`FairP` (CertiKOS's `CalBound`) is a hypothesis of the liveness theorems. Here
we exhibit a non-trivial environment that satisfies both `RelyP` and `FairP`,
for *every* CPU and *every* reachable starting log (any number of contenders,
any lock holder), so the liveness and refinement theorems are not vacuous.

* `Fill` is a new global invariant: every ticket in `[now, ticket)` belongs to
  some CPU. It replaces a pigeonhole argument. With it, "the next ticket to be
  served is owned by somebody" is immediate.
* `fairEnv` is a FIFO-fair scheduler for the other CPUs. Whenever CPU `c`
  looks at the shared memory, the current holder (if another CPU) releases;
  otherwise the owner of ticket `now` takes the lock (`hold`).
* `fairBound` is the `CalBound`-style counter: 1 when nobody holds the lock, 0
  otherwise.
* `acquire_correct_fair`, `acquire_refines_fair`: unconditional termination and
  atomic refinement of the C `acquire` under this scheduler.
-/

namespace Ticket

open ClightL

/-! ## The `Fill` invariant -/

def Fill (s : PState) : Prop :=
  ∀ t, s.now ≤ t → t < s.ticket → ∃ d, (s.phase d).tk = some t

theorem pstep_fill {s s' : PState} {e : Event} {o : Option HEvent}
    (hi : Inv s) (hf : Fill s) (hp : pstep s e = some (s', o)) : Fill s' := by
  obtain ⟨c, k⟩ := e
  simp only [pstep] at hp
  split at hp
  case isFalse => simp at hp
  cases k <;> cases hph : s.phase c <;> simp only [hph] at hp <;> try simp at hp
  · -- incTicket from idle: the new ticket goes to `c`
    obtain ⟨rfl, -⟩ := hp
    intro t h1 h2
    try dsimp only at h1 h2 ⊢
    by_cases ht : t = s.ticket
    · exact ⟨c, by simp [Phase.tk, ht]⟩
    · obtain ⟨d, hd⟩ := hf t h1 (by omega)
      have hdc : d ≠ c := by rintro rfl; rw [hph] at hd; simp [Phase.tk] at hd
      exact ⟨d, by simp only [setPhase_other _ _ hdc]; exact hd⟩
  · -- getNow: a pure read
    obtain ⟨rfl, -⟩ := hp; exact hf
  · -- incNow: the interval shrinks from below
    rename_i t0
    obtain ⟨rfl, -⟩ := hp
    have ht0 : t0 = s.now := hi.holdNow c t0 hph
    intro t h1 h2
    try dsimp only at h1 h2 ⊢
    obtain ⟨d, hd⟩ := hf t (by omega) h2
    have hdc : d ≠ c := by
      rintro rfl; rw [hph] at hd; simp [Phase.tk] at hd; omega
    exact ⟨d, by simp only [setPhase_other _ _ hdc]; exact hd⟩
  · -- hold: tickets unchanged
    rename_i t0
    obtain ⟨-, rfl, -⟩ := hp
    intro t h1 h2
    try dsimp only at h1 h2 ⊢
    obtain ⟨d, hd⟩ := hf t h1 h2
    refine ⟨d, ?_⟩
    by_cases hdc : d = c
    · subst hdc; rw [hph] at hd; simpa [Phase.tk] using hd
    · simp only [setPhase_other _ _ hdc]; exact hd

theorem replay_fill : ∀ {l : Log} {s : PState} {h : List HEvent},
    replay l = some (s, h) → Fill s
  | [], s, h, hr => by
    simp [replay] at hr; obtain ⟨rfl, -⟩ := hr
    intro t h1 h2; simp [PState.init] at h1 h2 <;> omega
  | _ :: _, _, _, hr => by
    obtain ⟨s0, h0, o, hl, hp, -⟩ := replay_cons hr
    exact pstep_fill (replay_inv hl) (replay_fill hl) hp

/-! ## Searching for a CPU -/

def findCPU (p : CPU → Bool) : Nat → Option CPU
  | 0 => none
  | n + 1 =>
    match findCPU p n with
    | some d => some d
    | none => if p n then some n else none

theorem findCPU_some {p : CPU → Bool} : ∀ {n d}, findCPU p n = some d → p d = true ∧ d < n
  | 0, d, h => by simp [findCPU] at h
  | n + 1, d, h => by
    simp only [findCPU] at h
    split at h
    · rename_i d' heq
      simp at h; subst h
      have := findCPU_some heq
      exact ⟨this.1, Nat.lt_succ_of_lt this.2⟩
    · split at h
      · rename_i hpn; simp at h; subst h; exact ⟨hpn, Nat.lt_succ_self _⟩
      · simp at h

theorem findCPU_none {p : CPU → Bool} : ∀ {n}, findCPU p n = none → ∀ d, d < n → p d = false
  | 0, _, d, hd => absurd hd (by omega)
  | n + 1, h, d, hd => by
    simp only [findCPU] at h
    split at h
    · simp at h
    · rename_i heq
      split at h
      · simp at h
      · rename_i hpn
        by_cases hdn : d < n
        · exact findCPU_none heq d hdn
        · have : d = n := by omega
          subst this; simpa using hpn

theorem findCPU_isSome {p : CPU → Bool} {n d : Nat} (hp : p d = true) (hd : d < n) :
    (findCPU p n).isSome = true := by
  cases hq : findCPU p n with
  | none => have := findCPU_none hq d hd; simp_all
  | some _ => rfl

/-! ## The scheduler -/

def Phase.isHold : Phase → Bool
  | .holding _ => true
  | _ => false

/-- Another CPU `d` currently holds the lock. -/
def isHolding (s : PState) (c d : CPU) : Bool :=
  match s.phase d with
  | .holding _ => d != c
  | _ => false

/-- Another CPU `d` waits for the ticket being served right now. -/
def isNext (s : PState) (c d : CPU) : Bool :=
  match s.phase d with
  | .waiting t => (d != c) && (t == s.now)
  | _ => false

theorem isHolding_true {s : PState} {c d : CPU} (h : isHolding s c d = true) :
    d ≠ c ∧ ∃ t, s.phase d = .holding t := by
  unfold isHolding at h
  split at h
  · rename_i t ht; exact ⟨by simpa using h, t, ht⟩
  · simp at h

theorem isHolding_false {s : PState} {c d : CPU} {t : Nat} (h : isHolding s c d = false)
    (ht : s.phase d = .holding t) : d = c := by
  simpa [isHolding, ht] using h

theorem isNext_true {s : PState} {c d : CPU} (h : isNext s c d = true) :
    d ≠ c ∧ s.phase d = .waiting s.now := by
  unfold isNext at h
  split at h
  · rename_i t ht
    simp at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by rw [ht, h2]⟩
  · simp at h

/-- FIFO-fair scheduler for the CPUs other than the querying one. -/
def fairQuery (c : CPU) (l : Log) : List Event :=
  match replay l with
  | none => []
  | some (s, _) =>
    match findCPU (isHolding s c) NCPU with
    | some d => [⟨d, .incNow⟩]
    | none =>
      match findCPU (isNext s c) NCPU with
      | some d => [⟨d, .hold⟩]
      | none => []

def fairEnv : EnvCtx where
  query := fairQuery
  noSelf := by
    intro c l e he
    simp only [fairQuery] at he
    split at he
    · simp at he
    · rename_i s h _
      split at he
      · rename_i d hd
        simp at he; subst he
        exact (isHolding_true (findCPU_some hd).1).1
      · split at he
        · rename_i d hd
          simp at he; subst he
          exact (isNext_true (findCPU_some hd).1).1
        · simp at he

/-- `CalBound`-style counter: 1 when the lock is free, 0 when someone holds it. -/
def fairBound (l : Log) : Nat :=
  match replay l with
  | some (s, _) => if (findCPU (fun d => (s.phase d).isHold) NCPU).isSome then 0 else 1
  | none => 0

theorem fairEnv_rely (c : CPU) : RelyP fairEnv c where
  conform := by
    intro l s h hl
    simp only [pull, fairEnv, fairQuery, hl]
    cases hfh : findCPU (isHolding s c) NCPU with
    | some d =>
      obtain ⟨hp, hd⟩ := findCPU_some hfh
      obtain ⟨_, t, ht⟩ := isHolding_true hp
      exact replay_cons_some hl (by simp [pstep, hd, ht])
    | none =>
      cases hfn : findCPU (isNext s c) NCPU with
      | some d =>
        obtain ⟨hp, hd⟩ := findCPU_some hfn
        obtain ⟨_, hw⟩ := isNext_true hp
        exact replay_cons_some hl (by simp [pstep, hd, hw])
      | none => exact ⟨s, h, by simpa using hl⟩

/-- **The scheduler is fair**, for every CPU and every ticket it waits for. -/
theorem fairEnv_fair (c : CPU) (tn : Nat) (hc : c < NCPU) : FairP fairEnv c tn fairBound := by
  intro l s h hl hw hlt
  cases hfh : findCPU (isHolding s c) NCPU with
  | some d =>
    -- the holder releases: `now` grows
    left
    have hpull : pull fairEnv c l = ⟨d, .incNow⟩ :: l := by
      simp [pull, fairEnv, fairQuery, hl, hfh]
    rw [hpull]; simp [now, countK]
  | none =>
    -- nobody holds the lock: the owner of ticket `now` takes it; the bound drops
    right
    have hi := replay_inv hl
    have htk : tn < s.ticket := hi.tkLt c tn (by simp [hw, Phase.tk])
    have hnohold : ∀ e t, s.phase e = .holding t → False := by
      intro e t he
      by_cases hen : e < NCPU
      · have hec := isHolding_false (findCPU_none hfh e hen) he
        subst hec; rw [hw] at he; cases he
      · rw [hi.idleOut e (Nat.le_of_not_lt hen)] at he; cases he
    obtain ⟨d, hd⟩ := replay_fill hl s.now (Nat.le_refl _) (by omega)
    have hdc : d ≠ c := by rintro rfl; rw [hw] at hd; simp [Phase.tk] at hd; omega
    have hdlt : d < NCPU := by
      apply Nat.lt_of_not_le; intro hge
      rw [hi.idleOut d hge] at hd; simp [Phase.tk] at hd
    have hdw : s.phase d = .waiting s.now := by
      cases hph : s.phase d with
      | idle => rw [hph] at hd; simp [Phase.tk] at hd
      | waiting t => rw [hph] at hd; simp [Phase.tk] at hd; rw [hd]
      | holding t => exact (hnohold d t hph).elim
    cases hfn : findCPU (isNext s c) NCPU with
    | none =>
      exfalso
      have h1 := findCPU_none hfn d hdlt
      simp [isNext, hdw, hdc] at h1
    | some d' =>
      obtain ⟨hp, hd'lt⟩ := findCPU_some hfn
      obtain ⟨hd'c, hd'w⟩ := isNext_true hp
      have hpull : pull fairEnv c l = ⟨d', .hold⟩ :: l := by
        simp [pull, fairEnv, fairQuery, hl, hfh, hfn]
      rw [hpull]
      have hb : fairBound l = 1 := by
        simp only [fairBound, hl]
        cases hq : findCPU (fun d => (s.phase d).isHold) NCPU with
        | none => rfl
        | some e =>
          exfalso
          have := (findCPU_some hq).1
          cases he : s.phase e with
          | idle => simp [he, Phase.isHold] at this
          | waiting _ => simp [he, Phase.isHold] at this
          | holding t => exact hnohold e t he
      have hp1 : pstep s ⟨d', .hold⟩ =
          some (⟨s.ticket, s.now, setPhase s.phase d' (.holding s.now)⟩, some (.acq d')) := by
        simp [pstep, hd'lt, hd'w]
      have hp2 : pstep ⟨s.ticket, s.now, setPhase s.phase d' (.holding s.now)⟩ ⟨c, .getNow⟩ =
          some (⟨s.ticket, s.now, setPhase s.phase d' (.holding s.now)⟩, none) := by
        simp [pstep, hc, setPhase_other _ _ (Ne.symm hd'c), hw]
      have hr2 := replay_cons_of (replay_cons_of hl hp1) hp2
      have hb' : fairBound (⟨c, .getNow⟩ :: ⟨d', .hold⟩ :: l) = 0 := by
        simp only [fairBound]
        rw [hr2]
        dsimp only
        split
        · rfl
        · rename_i hneg
          exfalso; apply hneg
          exact findCPU_isSome (d := d') (by simp [Phase.isHold]) hd'lt
      omega

/-! ## Unconditional liveness and refinement under the fair scheduler -/

/-- Under `fairEnv`, `acquire` (C code) terminates from any reachable log in
which `c` is idle, and its result satisfies the guarantee. -/
theorem acquire_correct_fair {c : CPU} (hc : c < NCPU) {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle) (loc : Locals) :
    (∃ loc' r, Star (prims fairEnv c) ⟨acquireCode, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
        AcqPost c (ticket (pull fairEnv c l)) h r) ∧
      ¬ Diverges (prims fairEnv c) ⟨acquireCode, .stop, loc, l⟩ :=
  acquire_correct hc (fairEnv_rely c) hl hidle fairBound (fairEnv_fair c _ hc) loc

/-- Under `fairEnv`, the C `acquire` refines the atomic L1 `acq`. -/
theorem acquire_refines_fair {c : CPU} (hc : c < NCPU) {l : Log} {s : PState} {h : HLog}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle) (loc : Locals) :
    ∃ (εH : HEnv) (loc' : Locals) (r : Log) (h' : HLog),
      HRely εH c ∧
      Star (prims fairEnv c) ⟨acquireCode, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ ∧
      ¬ Diverges (prims fairEnv c) ⟨acquireCode, .stop, loc, l⟩ ∧
      hprims εH c .acq [] h = some (0, h') ∧
      Star (hprims εH c) ⟨acqCodeH, .stop, loc, h⟩ ⟨.skip, .stop, loc.set "_" 0, h'⟩ ∧
      RelLog r h' :=
  acquire_refines_atomic hc (fairEnv_rely c) hl hidle fairBound (fairEnv_fair c _ hc) loc

theorem fairBound_le (l : Log) : fairBound l ≤ 1 := by
  unfold fairBound; split
  · split <;> omega
  · omega

/-- Under `fairEnv`, `acquire` returns within `(NCPU + 1) * 2 = 18` loop
iterations, from any reachable log. CertiKOS's Lemma 6 gives `n × m × k`. -/
theorem acquire_bounded_fair {c : CPU} (hc : c < NCPU) {l : Log} {s : PState} {h : List HEvent}
    (hl : replay l = some (s, h)) (hidle : s.phase c = .idle) :
    ∃ r, acquireSpec fairEnv c ((NCPU + 1) * (1 + 1)) l = some r :=
  acquire_live_bounded hc (fairEnv_rely c) hl hidle fairBound 1 fairBound_le (fairEnv_fair c _ hc)

/-! ## A concrete contended run -/

/-- CPU 1 holds the lock; CPUs 2 and 3 are queued behind it. -/
def contendedLog : Log :=
  [⟨3, .incTicket⟩, ⟨2, .incTicket⟩, ⟨1, .hold⟩, ⟨1, .getNow⟩, ⟨1, .incTicket⟩]

/-- CPU 0 joins the queue as fourth and gets the lock (checked by evaluation). -/
theorem demo_contended : (acquireSpec fairEnv 0 8 contendedLog).isSome = true := by
  decide

end Ticket
