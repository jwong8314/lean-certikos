import CertiKOS.TicketPy
import CertiKOS.TicketProtocol
import CertiKOS.ClightToPyLive

/-!
# Liveness of the ticket-lock client, on the C machine and in Python

`TicketPy.lean` proves the C machine and the Python pool equivalent on
reachable states. Here liveness crosses over too.

**C side: a termination certificate** (`cert`, a `ClightToPy.LiveCert`).
* `At N c s t w`: CPU `c`'s configuration `t` is one of the 24 program points
  of the client loop, consistent with the protocol state `s` of the shared log,
  and has weight `w`. The weight counts the steps left, except that the three
  points of the wait loop all weigh 16 while `now < tn`.
* The potential `Φ` is the sum of the weights. A step of any CPU never raises
  it. A step of a CPU that is not spinning (`Spins`) lowers it. When `now`
  reaches a waiter's ticket, that waiter's weight drops below 16.
* Some unfinished CPU is never spinning: the CPU whose ticket is `now`
  (`Cover`: every ticket in `[now, ticket)` belongs to some CPU). This is the
  global form of the per-CPU fairness argument (`FairP`, `loop_live`) in
  `TicketProtocol.lean`. The CPU holding the current turn must make progress.

**Python side** (`python_live`): for `T ≤ NCPU` threads running the
translated client `N` times each,
* `python_fair_terminates`: every `K`-fair run has fewer than
  `11 * K * (T * (25 * N + 4) + 1)` steps;
* `python_no_deadlock`: no reachable state is stuck unless every thread has
  finished;
* `python_final`: a finished pool has `lk.ticket == lk.now`.

So under any scheduler that, within every `K` steps, runs each unfinished
thread (including letting it into `with L:`), every thread finishes all `N`
acquire/release rounds.
-/

namespace TicketLive

open ClightL Ticket ClightToPy TicketPy
open PyL (Pool Heap MStep MSteps)

/-! ## The client code, point by point -/

def gI (N : Nat) : ClightL.Expr := .bin .ne (.var "i") (.const (BitVec.ofNat 32 N))
def incI : Stmt Prim := .assign "i" (.bin .add (.var "i") (.const 1))
def bodyS : Stmt Prim := .seq acquireCode (.seq releaseCode incI)
def loopS (N : Nat) : Stmt Prim := .while (gI N) bodyS
def gnC : Stmt Prim := .call "n" .getNow []
def lgE : ClightL.Expr := .bin .ne (.var "n") (.var "t")

def KO (N : Nat) : Cont Prim := .loop (gI N) bodyS .stop
def KA (N : Nat) : Cont Prim := .seq (.seq releaseCode incI) (KO N)
def KT (N : Nat) : Cont Prim := .seq (.seq gnC (.seq acquireLoop holdCall)) (KA N)
def KW (N : Nat) : Cont Prim := .seq (.seq acquireLoop holdCall) (KA N)
def KH (N : Nat) : Cont Prim := .seq holdCall (KA N)
def KL (N : Nat) : Cont Prim := .loop lgE gnC (KH N)
def KR (N : Nat) : Cont Prim := .seq incI (KO N)

theorem clientCode_eq (N : Nat) : clientCode N = .seq (.assign "i" (.const 0)) (loopS N) := rfl

/-! ## The turn invariant of the protocol -/

/-- Every outstanding ticket belongs to some CPU. -/
def Cover (s : PState) : Prop := ∀ v, s.now ≤ v → v < s.ticket → ∃ d, (s.phase d).tk = some v

theorem pstep_cover {s s' : PState} {e : Event} {o : Option HEvent} (hi : Inv s) (hc : Cover s)
    (hp : pstep s e = some (s', o)) : Cover s' := by
  obtain ⟨c, k⟩ := e
  simp only [pstep] at hp
  split at hp
  case isFalse => simp at hp
  try simp only at hp
  cases k <;> cases hph : s.phase c <;> simp only [hph] at hp <;> try simp at hp
  · -- incTicket from idle
    obtain ⟨rfl, -⟩ := hp
    intro v hv1 hv2
    simp only at hv1 hv2 ⊢
    by_cases hvt : v = s.ticket
    · exact ⟨c, by simp [hvt, Phase.tk]⟩
    · obtain ⟨d, hd⟩ := hc v hv1 (by omega)
      have hdc : d ≠ c := by rintro rfl; simp [hph, Phase.tk] at hd
      exact ⟨d, by rw [setPhase_other _ _ hdc]; exact hd⟩
  · -- getNow
    obtain ⟨rfl, -⟩ := hp; exact hc
  · -- incNow from holding
    rename_i t
    obtain ⟨rfl, -⟩ := hp
    intro v hv1 hv2
    simp only at hv1 hv2 ⊢
    obtain ⟨d, hd⟩ := hc v (by omega) hv2
    have ht := hi.holdNow c t hph
    have hdc : d ≠ c := by rintro rfl; simp [hph, Phase.tk] at hd; omega
    exact ⟨d, by rw [setPhase_other _ _ hdc]; exact hd⟩
  · -- hold
    rename_i t
    obtain ⟨-, rfl, -⟩ := hp
    intro v hv1 hv2
    obtain ⟨d, hd⟩ := hc v hv1 hv2
    by_cases hdc : d = c
    · subst hdc; exact ⟨d, by simp only [setPhase_same, Phase.tk]; simpa [hph, Phase.tk] using hd⟩
    · exact ⟨d, by simp only; rw [setPhase_other _ _ hdc]; exact hd⟩

theorem replay_cover : ∀ {l : Log} {s : PState} {h : List HEvent}, replay l = some (s, h) → Cover s
  | [], s, h, hr => by
    simp [replay] at hr; obtain ⟨rfl, -⟩ := hr
    intro v _ hv; simp [PState.init] at hv
  | _ :: _, _, _, hr => by
    obtain ⟨s0, h0, o, hl, hp, -⟩ := replay_cons hr
    exact pstep_cover (replay_inv hl) (replay_cover hl) hp

/-- `now` only grows, and only the lock holder moves it. -/
theorem pstep_now {s s' : PState} {e : Event} {o : Option HEvent} (hp : pstep s e = some (s', o)) :
    s.now ≤ s'.now ∧ (s'.now ≠ s.now → ∃ t, s.phase e.cpu = .holding t) := by
  obtain ⟨c, k⟩ := e
  simp only [pstep] at hp
  split at hp
  case isFalse => simp at hp
  try simp only at hp
  cases k <;> cases hph : s.phase c <;> simp only [hph] at hp <;> try simp at hp
  · obtain ⟨rfl, -⟩ := hp; simp
  · obtain ⟨rfl, -⟩ := hp; simp
  · obtain ⟨rfl, -⟩ := hp; exact ⟨by simp, fun _ => ⟨_, rfl⟩⟩
  · obtain ⟨-, rfl, -⟩ := hp; simp

/-- While CPU `d` waits for the current turn, nobody else can move `now`. -/
theorem now_stays {s s' : PState} {e : Event} {o : Option HEvent} (hi : Inv s)
    (hp : pstep s e = some (s', o)) {d : CPU} (hne : e.cpu ≠ d) {tn : Nat}
    (hw : s.phase d = .waiting tn) (hn : s.now = tn) : s'.now = tn := by
  obtain ⟨hle, hch⟩ := pstep_now hp
  refine Classical.byContradiction fun hc => ?_
  obtain ⟨t, ht⟩ := hch (by omega)
  have := hi.holdNow _ _ ht
  exact hne (hi.uniq _ d tn (by simp [ht, Phase.tk]; omega) (by simp [hw, Phase.tk]))

/-! ## Program points and weights -/

/-- Inside iteration `m` of the outer loop. -/
def Iter (N : Nat) (σ : Locals) (m : Nat) : Prop := m < N ∧ σ "i" = BitVec.ofNat 32 m

/-- Waiting for ticket `tn`, which is in `t`. -/
def Wt (c : CPU) (s : PState) (σ : Locals) (tn : Nat) : Prop :=
  s.phase c = .waiting tn ∧ σ "t" = BitVec.ofNat 32 tn

/-- `n` holds a value of `now` read while waiting for `tn`. -/
def NInv (σ : Locals) (s : PState) (tn : Nat) : Prop :=
  ∃ v, v ≤ s.now ∧ tn ≤ v + NCPU ∧ σ "n" = BitVec.ofNat 32 v

def w12 (s : PState) (tn : Nat) (σ : Locals) : Nat :=
  if s.now = tn then (if σ "n" = σ "t" then 11 else 14) else 16
def w13 (s : PState) (tn : Nat) : Nat := if s.now = tn then 13 else 16
def w14 (s : PState) (tn : Nat) (σ : Locals) : Nat :=
  if s.now = tn then (if σ "n" = σ "t" then 12 else 15) else 16

/-- CPU `c` is at a program point of the client, consistent with the protocol
state `s`, with weight `w`. -/
inductive At (N : Nat) (c : CPU) (s : PState) : CThread Prim → Nat → Prop
  | p0 {σ} : s.phase c = .idle → At N c s ⟨clientCode N, .stop, σ⟩ (N * 25 + 4)
  | p1 {σ} : s.phase c = .idle →
      At N c s ⟨.assign "i" (.const 0), .seq (loopS N) .stop, σ⟩ (N * 25 + 3)
  | p2 {σ} : s.phase c = .idle → σ "i" = 0 → At N c s ⟨.skip, .seq (loopS N) .stop, σ⟩ (N * 25 + 2)
  | p3 {σ m} : s.phase c = .idle → m ≤ N → σ "i" = BitVec.ofNat 32 m →
      At N c s ⟨loopS N, .stop, σ⟩ ((N - m) * 25 + 1)
  | p4 {σ m} : s.phase c = .idle → Iter N σ m → At N c s ⟨bodyS, KO N, σ⟩ ((N - m - 1) * 25 + 24)
  | p5 {σ m} : s.phase c = .idle → Iter N σ m →
      At N c s ⟨acquireCode, KA N, σ⟩ ((N - m - 1) * 25 + 23)
  | p6 {σ m} : s.phase c = .idle → Iter N σ m →
      At N c s ⟨.call "t" .faiTicket [], KT N, σ⟩ ((N - m - 1) * 25 + 22)
  | p7 {σ m tn} : Wt c s σ tn → Iter N σ m → At N c s ⟨.skip, KT N, σ⟩ ((N - m - 1) * 25 + 21)
  | p8 {σ m tn} : Wt c s σ tn → Iter N σ m →
      At N c s ⟨.seq gnC (.seq acquireLoop holdCall), KA N, σ⟩ ((N - m - 1) * 25 + 20)
  | p9 {σ m tn} : Wt c s σ tn → Iter N σ m → At N c s ⟨gnC, KW N, σ⟩ ((N - m - 1) * 25 + 19)
  | p10 {σ m tn} : Wt c s σ tn → Iter N σ m → NInv σ s tn →
      At N c s ⟨.skip, KW N, σ⟩ ((N - m - 1) * 25 + 18)
  | p11 {σ m tn} : Wt c s σ tn → Iter N σ m → NInv σ s tn →
      At N c s ⟨.seq acquireLoop holdCall, KA N, σ⟩ ((N - m - 1) * 25 + 17)
  | p12 {σ m tn} : Wt c s σ tn → Iter N σ m → NInv σ s tn →
      At N c s ⟨acquireLoop, KH N, σ⟩ ((N - m - 1) * 25 + w12 s tn σ)
  | p13 {σ m tn} : Wt c s σ tn → Iter N σ m →
      At N c s ⟨gnC, KL N, σ⟩ ((N - m - 1) * 25 + w13 s tn)
  | p14 {σ m tn} : Wt c s σ tn → Iter N σ m → NInv σ s tn →
      At N c s ⟨.skip, KL N, σ⟩ ((N - m - 1) * 25 + w14 s tn σ)
  | p15 {σ m tn} : Wt c s σ tn → Iter N σ m → s.now = tn →
      At N c s ⟨.skip, KH N, σ⟩ ((N - m - 1) * 25 + 10)
  | p16 {σ m tn} : Wt c s σ tn → Iter N σ m → s.now = tn →
      At N c s ⟨holdCall, KA N, σ⟩ ((N - m - 1) * 25 + 9)
  | p17 {σ m tn} : s.phase c = .holding tn → Iter N σ m →
      At N c s ⟨.skip, KA N, σ⟩ ((N - m - 1) * 25 + 8)
  | p18 {σ m tn} : s.phase c = .holding tn → Iter N σ m →
      At N c s ⟨.seq releaseCode incI, KO N, σ⟩ ((N - m - 1) * 25 + 7)
  | p19 {σ m tn} : s.phase c = .holding tn → Iter N σ m →
      At N c s ⟨releaseCode, KR N, σ⟩ ((N - m - 1) * 25 + 6)
  | p20 {σ m} : s.phase c = .idle → Iter N σ m → At N c s ⟨.skip, KR N, σ⟩ ((N - m - 1) * 25 + 5)
  | p21 {σ m} : s.phase c = .idle → Iter N σ m → At N c s ⟨incI, KO N, σ⟩ ((N - m - 1) * 25 + 4)
  | p22 {σ m} : s.phase c = .idle → m < N → σ "i" = BitVec.ofNat 32 (m + 1) →
      At N c s ⟨.skip, KO N, σ⟩ ((N - m - 1) * 25 + 2)
  | done {σ} : s.phase c = .idle → At N c s ⟨.skip, .stop, σ⟩ 0

/-- The three points of the wait loop. -/
def InLoop (N : Nat) (t : CThread Prim) : Prop :=
  (t.stmt = acquireLoop ∧ t.cont = KH N) ∨ t.cont = KL N

/-- CPU `c` is spinning: in the wait loop, and its turn has not come. -/
def Spins (N : Nat) (c : CPU) (l : Log) (t : CThread Prim) : Prop :=
  ∃ s h tn, replay l = some (s, h) ∧ s.phase c = .waiting tn ∧ s.now < tn ∧ InLoop N t

/-! ## Small facts -/

theorem ne_eval_zero (σ : Locals) (a b : ClightL.Expr) :
    (ClightL.Expr.bin .ne a b).eval σ = 0 ↔ a.eval σ = b.eval σ := by
  simp only [ClightL.Expr.eval, ClightL.BinOp.eval]
  by_cases h : a.eval σ = b.eval σ <;> simp [h]

theorem ofNat_succ (m : Nat) : BitVec.ofNat 32 m + 1 = BitVec.ofNat 32 (m + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add] <;> omega

theorem w12_le (s : PState) (tn : Nat) (σ : Locals) : w12 s tn σ ≤ 16 := by
  unfold w12; split <;> (try split) <;> omega

theorem w12_mono {s s' : PState} {tn : Nat} {σ : Locals} (h : s.now = tn → s'.now = tn) :
    w12 s' tn σ ≤ w12 s tn σ := by
  unfold w12; by_cases h1 : s.now = tn
  · simp [h1, h h1]
  · simp only [h1, ite_false]; split <;> (try split) <;> omega

theorem w13_mono {s s' : PState} {tn : Nat} (h : s.now = tn → s'.now = tn) : w13 s' tn ≤ w13 s tn := by
  unfold w13; by_cases h1 : s.now = tn
  · simp [h1, h h1]
  · simp only [h1, ite_false]; split <;> omega

theorem w14_mono {s s' : PState} {tn : Nat} {σ : Locals} (h : s.now = tn → s'.now = tn) :
    w14 s' tn σ ≤ w14 s tn σ := by
  unfold w14; by_cases h1 : s.now = tn
  · simp [h1, h h1]
  · simp only [h1, ite_false]; split <;> (try split) <;> omega

/-- Leaving the wait loop means it is our turn. -/
theorem nInv_exit {c : CPU} {s : PState} {σ : Locals} {tn : Nat} (hi : Inv s) (hw : Wt c s σ tn)
    (hn : NInv σ s tn) (heq : σ "n" = σ "t") : s.now = tn := by
  obtain ⟨v, hv1, hv2, hv3⟩ := hn
  have hle := hi.waitGe c tn hw.1
  rw [hv3, hw.2] at heq
  have := ofNat_eq_of_close (by omega) (by simp only [NCPU] at hv2; omega) heq
  omega

/-- A fresh `get_n` re-establishes `NInv`. -/
theorem nInv_fresh {c : CPU} {s : PState} {tn : Nat} (hi : Inv s) (hw : s.phase c = .waiting tn)
    (σ : Locals) : NInv (σ.set "n" (BitVec.ofNat 32 s.now)) s tn := by
  have h1 := hi.tkLt c tn (by simp [hw, Phase.tk])
  have h2 := hi.outstanding_le
  exact ⟨s.now, Nat.le_refl _, by omega, by simp⟩

theorem spins_of {N : Nat} {c : CPU} {l : Log} {s : PState} {h : List HEvent} {t : CThread Prim}
    {tn : Nat} (hl : replay l = some (s, h)) (hi : Inv s) (hw : s.phase c = .waiting tn)
    (hne : ¬ s.now = tn) (hL : InLoop N t) : Spins N c l t :=
  ⟨s, h, tn, hl, hw, by have := hi.waitGe c tn hw; omega, hL⟩

/-! ## One step of one CPU -/

/-- **One step of CPU `c`**: it lands on another program point, the log grows
by at most one legal event of `c`, and the weight goes down, unless `c` is
spinning, in which case it stays the same. -/
theorem own_step {N : Nat} {c : CPU} {s : PState} {h : List HEvent} {l : Log} {t : CThread Prim}
    {w : Nat} {c' : Config Prim Log} (hc : c < NCPU) (hN : N < 2 ^ 32)
    (hl : replay l = some (s, h)) (hA : At N c s t w)
    (hst : ClightL.step (prims noEnv c) (t.cfg l) = some c') :
    ∃ s', ((c'.abs = l ∧ s' = s) ∨ ∃ k o, c'.abs = ⟨c, k⟩ :: l ∧ pstep s ⟨c, k⟩ = some (s', o)) ∧
      ∃ w', At N c s' (thr c') w' ∧ (w' < w ∨ (w' = w ∧ Spins N c l t)) := by
  have hi := replay_inv hl
  obtain ⟨hn, htk⟩ := replay_counts hl
  cases hA with
  | p0 hp =>
    simp only [ClightL.step, CThread.cfg, clientCode, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p1 hp, .inl (by omega)⟩
  | p1 hp =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p2 hp (by simp [ClightL.Expr.eval]), .inl (by omega)⟩
  | @p2 σ hp hi0 =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p3 (m := 0) hp (Nat.zero_le _) (by show σ "i" = _; rw [hi0]; rfl),
      .inl (by omega)⟩
  | @p3 σ m hp hm hiv =>
    change ClightL.step _ (CThread.cfg ⟨.while (gI N) bodyS, .stop, σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    by_cases hz : (gI N).eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have hmN : m = N := by
        rw [gI, ne_eval_zero] at hz; simp only [ClightL.Expr.eval] at hz; rw [hiv] at hz
        exact ofNat_eq_of_close hm (by omega) hz
      exact ⟨s, .inl ⟨rfl, rfl⟩, 0, .done hp, .inl (by omega)⟩
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      have hmN : m < N := by
        refine Nat.lt_of_le_of_ne hm fun he => hz ?_
        rw [gI, ne_eval_zero]; simp only [ClightL.Expr.eval]; rw [hiv, he]
      exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p4 hp ⟨hmN, hiv⟩, .inl (by omega)⟩
  | p4 hp hit =>
    simp only [ClightL.step, CThread.cfg, bodyS, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p5 hp hit, .inl (by omega)⟩
  | p5 hp hit =>
    simp only [ClightL.step, CThread.cfg, acquireCode, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p6 hp hit, .inl (by omega)⟩
  | @p6 σ m hp hit =>
    simp only [ClightL.step, CThread.cfg, prims, List.map_nil, pull_noEnv, Option.some.injEq] at hst
    subst hst
    refine ⟨⟨s.ticket + 1, s.now, setPhase s.phase c (.waiting s.ticket)⟩,
      .inr ⟨.incTicket, none, rfl, by simp [pstep, hc, hp]⟩, _, .p7 (tn := s.ticket)
        ⟨by simp, by simp [htk]⟩ ⟨hit.1, by simp [hit.2]⟩, .inl (by omega)⟩
  | p7 hw hit =>
    simp only [ClightL.step, CThread.cfg, KT, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p8 hw hit, .inl (by omega)⟩
  | p8 hw hit =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p9 hw hit, .inl (by omega)⟩
  | @p9 σ m tn hw hit =>
    simp only [ClightL.step, CThread.cfg, gnC, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    refine ⟨s, .inr ⟨.getNow, none, rfl, by simp [pstep, hc, hw.1]⟩, _,
      .p10 ⟨hw.1, by simp [hw.2]⟩ ⟨hit.1, by simp [hit.2]⟩ ?_, .inl (by omega)⟩
    rw [← hn]; exact nInv_fresh hi hw.1 σ
  | p10 hw hit hni =>
    simp only [ClightL.step, CThread.cfg, KW, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p11 hw hit hni, .inl (by omega)⟩
  | @p11 σ m tn hw hit hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p12 hw hit hni, .inl (by dsimp only; have := w12_le s tn σ; omega)⟩
  | @p12 σ m tn hw hit hni =>
    change ClightL.step _ (CThread.cfg ⟨.while lgE gnC, KH N, σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    by_cases hz : lgE.eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have heq : σ "n" = σ "t" := by rw [lgE, ne_eval_zero] at hz; simpa [ClightL.Expr.eval] using hz
      have hnow := nInv_exit hi hw hni heq
      refine ⟨s, .inl ⟨rfl, rfl⟩, _, .p15 hw hit hnow, .inl ?_⟩
      simp [w12, hnow, heq]
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      have hne : ¬ σ "n" = σ "t" := by
        intro h; apply hz; rw [lgE, ne_eval_zero]; simpa [ClightL.Expr.eval] using h
      refine ⟨s, .inl ⟨rfl, rfl⟩, _, .p13 hw hit, ?_⟩
      by_cases hnow : s.now = tn
      · left; simp [w12, w13, hnow, hne]
      · right; refine ⟨by simp [w12, w13, hnow], ?_⟩
        exact spins_of hl hi hw.1 hnow (.inl ⟨rfl, rfl⟩)
  | @p13 σ m tn hw hit =>
    simp only [ClightL.step, CThread.cfg, gnC, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    refine ⟨s, .inr ⟨.getNow, none, rfl, by simp [pstep, hc, hw.1]⟩, _,
      .p14 ⟨hw.1, by simp [hw.2]⟩ ⟨hit.1, by simp [hit.2]⟩ (by rw [← hn]; exact nInv_fresh hi hw.1 σ),
      ?_⟩
    by_cases hnow : s.now = tn
    · left
      have e2 : BitVec.ofNat 32 (now l) = σ "t" := by rw [hw.2, ← hn, hnow]
      simp [w13, w14, hnow, e2]
    · right; refine ⟨by simp [w13, w14, hnow], ?_⟩
      exact spins_of hl hi hw.1 hnow (.inr rfl)
  | @p14 σ m tn hw hit hni =>
    simp only [ClightL.step, CThread.cfg, KL, Option.some.injEq] at hst; subst hst
    refine ⟨s, .inl ⟨rfl, rfl⟩, _, .p12 hw hit hni, ?_⟩
    by_cases hnow : s.now = tn
    · left; simp only [w12, w14, hnow, ite_true]; split <;> omega
    · right; refine ⟨by simp [w12, w14, hnow], ?_⟩
      exact spins_of hl hi hw.1 hnow (.inr rfl)
  | p15 hw hit hnow =>
    simp only [ClightL.step, CThread.cfg, KH, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p16 hw hit hnow, .inl (by omega)⟩
  | @p16 σ m tn hw hit hnow =>
    simp only [ClightL.step, CThread.cfg, holdCall, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    refine ⟨⟨s.ticket, s.now, setPhase s.phase c (.holding tn)⟩,
      .inr ⟨.hold, some (.acq c), rfl, by simp [pstep, hc, hw.1, hnow]⟩, _,
      .p17 (tn := tn) (by simp) ⟨hit.1, by simp [hit.2]⟩, .inl (by omega)⟩
  | p17 hh hit =>
    simp only [ClightL.step, CThread.cfg, KA, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p18 hh hit, .inl (by omega)⟩
  | p18 hh hit =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p19 hh hit, .inl (by omega)⟩
  | @p19 σ m tn hh hit =>
    simp only [ClightL.step, CThread.cfg, releaseCode, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    refine ⟨⟨s.ticket, s.now + 1, setPhase s.phase c .idle⟩,
      .inr ⟨.incNow, some (.rel c), rfl, by simp [pstep, hc, hh]⟩, _,
      .p20 (by simp) ⟨hit.1, by simp [hit.2]⟩, .inl (by omega)⟩
  | p20 hp hit =>
    simp only [ClightL.step, CThread.cfg, KR, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p21 hp hit, .inl (by omega)⟩
  | @p21 σ m hp hit =>
    simp only [ClightL.step, CThread.cfg, incI, Option.some.injEq] at hst; subst hst
    refine ⟨s, .inl ⟨rfl, rfl⟩, _, .p22 hp hit.1 ?_, .inl (by omega)⟩
    simp only [Locals.set_same, ClightL.Expr.eval, ClightL.BinOp.eval, hit.2]; exact ofNat_succ m
  | @p22 σ m hp hm hi1 =>
    simp only [ClightL.step, CThread.cfg, KO, Option.some.injEq] at hst; subst hst
    exact ⟨s, .inl ⟨rfl, rfl⟩, _, .p3 (m := m + 1) hp hm hi1, .inl (by omega)⟩
  | done hp => simp [ClightL.step, CThread.cfg] at hst

/-- An event of another CPU never raises our weight. -/
theorem at_other {N : Nat} {d : CPU} {s s' : PState} {e : Event} {o : Option HEvent}
    {t : CThread Prim} {w : Nat} (hi : Inv s) (hp : pstep s e = some (s', o)) (hne : e.cpu ≠ d)
    (hA : At N d s t w) : ∃ w', w' ≤ w ∧ At N d s' t w' := by
  have hph : s'.phase d = s.phase d := (pstep_other hp hne).1
  have hnow : s.now ≤ s'.now := (pstep_now hp).1
  have hW : ∀ {σ tn}, Wt d s σ tn → Wt d s' σ tn := fun hw => ⟨by rw [hph]; exact hw.1, hw.2⟩
  have hN : ∀ {σ tn}, NInv σ s tn → NInv σ s' tn := fun ⟨v, h1, h2, h3⟩ => ⟨v, by omega, h2, h3⟩
  have hS : ∀ {σ tn}, Wt d s σ tn → s.now = tn → s'.now = tn := fun hw hn =>
    now_stays hi hp hne hw.1 hn
  have hI : s.phase d = .idle → s'.phase d = .idle := fun h => by rw [hph]; exact h
  have hH : ∀ {tn}, s.phase d = .holding tn → s'.phase d = .holding tn := fun h => by rw [hph]; exact h
  cases hA with
  | p0 hp => exact ⟨_, Nat.le_refl _, .p0 (hI hp)⟩
  | p1 hp => exact ⟨_, Nat.le_refl _, .p1 (hI hp)⟩
  | p2 hp h2 => exact ⟨_, Nat.le_refl _, .p2 (hI hp) h2⟩
  | p3 hp h2 h3 => exact ⟨_, Nat.le_refl _, .p3 (hI hp) h2 h3⟩
  | p4 hp h2 => exact ⟨_, Nat.le_refl _, .p4 (hI hp) h2⟩
  | p5 hp h2 => exact ⟨_, Nat.le_refl _, .p5 (hI hp) h2⟩
  | p6 hp h2 => exact ⟨_, Nat.le_refl _, .p6 (hI hp) h2⟩
  | p7 hw h2 => exact ⟨_, Nat.le_refl _, .p7 (hW hw) h2⟩
  | p8 hw h2 => exact ⟨_, Nat.le_refl _, .p8 (hW hw) h2⟩
  | p9 hw h2 => exact ⟨_, Nat.le_refl _, .p9 (hW hw) h2⟩
  | p10 hw h2 h3 => exact ⟨_, Nat.le_refl _, .p10 (hW hw) h2 (hN h3)⟩
  | p11 hw h2 h3 => exact ⟨_, Nat.le_refl _, .p11 (hW hw) h2 (hN h3)⟩
  | @p12 σ m tn hw h2 h3 =>
    exact ⟨_, Nat.add_le_add_left (w12_mono (σ := σ) (hS hw)) _, .p12 (hW hw) h2 (hN h3)⟩
  | p13 hw h2 => exact ⟨_, Nat.add_le_add_left (w13_mono (hS hw)) _, .p13 (hW hw) h2⟩
  | @p14 σ m tn hw h2 h3 =>
    exact ⟨_, Nat.add_le_add_left (w14_mono (σ := σ) (hS hw)) _, .p14 (hW hw) h2 (hN h3)⟩
  | p15 hw h2 h3 => exact ⟨_, Nat.le_refl _, .p15 (hW hw) h2 (hS hw h3)⟩
  | p16 hw h2 h3 => exact ⟨_, Nat.le_refl _, .p16 (hW hw) h2 (hS hw h3)⟩
  | p17 hh h2 => exact ⟨_, Nat.le_refl _, .p17 (hH hh) h2⟩
  | p18 hh h2 => exact ⟨_, Nat.le_refl _, .p18 (hH hh) h2⟩
  | p19 hh h2 => exact ⟨_, Nat.le_refl _, .p19 (hH hh) h2⟩
  | p20 hp h2 => exact ⟨_, Nat.le_refl _, .p20 (hI hp) h2⟩
  | p21 hp h2 => exact ⟨_, Nat.le_refl _, .p21 (hI hp) h2⟩
  | p22 hp h2 h3 => exact ⟨_, Nat.le_refl _, .p22 (hI hp) h2 h3⟩
  | done hp => exact ⟨_, Nat.le_refl _, .done (hI hp)⟩

/-- A finished CPU is idle. -/
theorem at_done {N : Nat} {c : CPU} {s : PState} {t : CThread Prim} {w : Nat} (hA : At N c s t w)
    (hd : Done t) : s.phase c = .idle := by
  obtain ⟨h1, h2⟩ := hd
  cases hA <;> simp_all [KO, KA, KT, KW, KH, KL, KR, loopS, clientCode, acquireLoop, holdCall,
    releaseCode, gnC, incI, bodyS, acquireCode]

/-! ## The global potential -/

def sumTo (ws : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo ws n + ws n

theorem sumTo_le {ws ws' : Nat → Nat} : ∀ n, (∀ d, d < n → ws' d ≤ ws d) → sumTo ws' n ≤ sumTo ws n
  | 0, _ => Nat.le_refl _
  | n + 1, h => by
    simp only [sumTo]
    have := sumTo_le n (fun d hd => h d (by omega)); have := h n (by omega); omega

theorem sumTo_lt {ws ws' : Nat → Nat} {i : Nat} : ∀ n, (∀ d, d < n → ws' d ≤ ws d) → i < n →
    ws' i < ws i → sumTo ws' n < sumTo ws n
  | 0, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, hi, hlt => by
    simp only [sumTo]
    by_cases hin : i = n
    · subst hin; have := sumTo_le i (fun d hd => h d (by omega)); omega
    · have := sumTo_lt n (fun d hd => h d (by omega)) (by omega) hlt; have := h n (by omega); omega

theorem sumTo_const (w : Nat) : ∀ n, sumTo (fun _ => w) n = n * w
  | 0 => by simp [sumTo]
  | n + 1 => by simp only [sumTo, sumTo_const w n, Nat.succ_mul]

/-- **The global invariant**, with potential `Φ`: the log replays, CPUs
`≥ T` never ran, and every CPU sits at a program point consistent with the
protocol state. `Φ` is the sum of the weights. -/
def GI (N T : Nat) (cs : List (CThread Prim)) (l : Log) (Φ : Nat) : Prop :=
  ∃ (s : PState) (h : List HEvent) (ws : Nat → Nat), replay l = some (s, h) ∧ cs.length = T ∧ T ≤ NCPU ∧ N < 2 ^ 32 ∧
    (∀ d, T ≤ d → s.phase d = .idle) ∧ (∀ i (hi : i < cs.length), At N i s cs[i] (ws i)) ∧
    Φ = sumTo ws T

/-- Active: unfinished and not spinning. -/
def Act (N : Nat) (cs : List (CThread Prim)) (l : Log) (d : Nat) : Prop :=
  ∃ hd : d < cs.length, ¬ Done cs[d] ∧ ¬ Spins N d l cs[d]

theorem replay_eq {l : Log} {s s' : PState} {h h' : List HEvent} (h1 : replay l = some (s, h))
    (h2 : replay l = some (s', h')) : s = s' := by
  rw [h1] at h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2; exact h2.1

/-- **One C step.** The potential does not go up, it goes down if the CPU
that moved was not spinning, and other CPUs do not start spinning. -/
theorem gstep {N T : Nat} {cs cs' : List (CThread Prim)} {l l' : Log} {Φ i : Nat}
    (hG : GI N T cs l Φ) (hS : CStepI P i cs l cs' l') :
    ∃ Φ', GI N T cs' l' Φ' ∧ Φ' ≤ Φ ∧ (∀ hi : i < cs.length, ¬ Spins N i l cs[i] → Φ' < Φ) ∧
      (∀ d, d ≠ i → ∀ hd : d < cs.length, Spins N d l' cs[d] → Spins N d l cs[d]) := by
  obtain ⟨s, h, ws, hl, hlen, hT, hN, hidle, hAt, rfl⟩ := hG
  obtain ⟨hi, c', hstep, rfl, rfl⟩ := hS
  have hiN : i < NCPU := by omega
  obtain ⟨s', hlog, w', hA', hw'⟩ := own_step hiN hN hl (hAt i hi) hstep
  have hnew : ∃ h', replay c'.abs = some (s', h') ∧
      (∀ d, d ≠ i → ∀ t w, At N d s t w → ∃ w', w' ≤ w ∧ At N d s' t w') ∧
      (∀ d, d ≠ i → s'.phase d = s.phase d) ∧ s.now ≤ s'.now := by
    rcases hlog with ⟨he, rfl⟩ | ⟨k, o, he, hp⟩
    · exact ⟨h, by rw [he]; exact hl, fun d _ t w hA => ⟨w, Nat.le_refl _, hA⟩, fun _ _ => rfl,
        Nat.le_refl _⟩
    · exact ⟨consOpt o h, by rw [he]; exact replay_cons_of hl hp,
        fun d hd t w hA => at_other (replay_inv hl) hp (Ne.symm hd) hA,
        fun d hd => (pstep_other hp (Ne.symm hd)).1, (pstep_now hp).1⟩
  obtain ⟨h', hl', hoth, hph, hnow⟩ := hnew
  have hex : ∀ d, ∃ w, ∀ hd : d < cs.length, d ≠ i → w ≤ ws d ∧ At N d s' cs[d] w := by
    intro d
    by_cases hd : d < cs.length ∧ d ≠ i
    · obtain ⟨w, h1, h2⟩ := hoth d hd.2 _ _ (hAt d hd.1)
      exact ⟨w, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hd⟩
  let ws' : Nat → Nat := fun d => if d = i then w' else Classical.choose (hex d)
  have hws : ∀ d (hd : d < cs.length), d ≠ i → ws' d ≤ ws d ∧ At N d s' cs[d] (ws' d) := by
    intro d hd hne; simp only [ws', hne, ite_false]; exact Classical.choose_spec (hex d) hd hne
  have hwi : ws' i = w' := by simp [ws']
  have hwle : w' ≤ ws i := by rcases hw' with h | ⟨h, _⟩ <;> omega
  have hle : ∀ d, d < T → ws' d ≤ ws d := by
    intro d hd
    by_cases hdi : d = i
    · subst hdi; rw [hwi]; exact hwle
    · exact (hws d (by omega) hdi).1
  refine ⟨sumTo ws' T, ⟨s', h', ws', hl', by simp [hlen], hT, hN, ?_, ?_, rfl⟩, sumTo_le T hle,
    ?_, ?_⟩
  · intro d hd
    have hdi : d ≠ i := by omega
    rw [hph d hdi]; exact hidle d hd
  · intro j hj
    rw [List.getElem_set]; split
    · rename_i hij; subst hij; rw [hwi]; exact hA'
    · rename_i hij; exact (hws j (by simpa using hj) (Ne.symm hij)).2
  · intro _ hns
    refine sumTo_lt (i := i) T hle (by omega) ?_
    rw [hwi]; rcases hw' with h | ⟨_, h⟩
    · exact h
    · exact absurd h hns
  · intro d hd hdl ⟨s2, h2, tn, hr2, hw2, hlt2, hL⟩
    have := replay_eq hl' hr2; subst this
    exact ⟨s, h, tn, hl, by rw [← hph d hd]; exact hw2, by omega, hL⟩

/-- **Some unfinished CPU is active**: if a CPU spins, the CPU whose ticket
is `now` is unfinished and not spinning. -/
theorem act_exists {N T : Nat} {cs : List (CThread Prim)} {l : Log} {Φ : Nat} (hG : GI N T cs l Φ)
    (hex : ∃ i, ∃ hi : i < cs.length, ¬ Done cs[i]) : ∃ d, Act N cs l d := by
  obtain ⟨s, h, ws, hl, hlen, hT, hN, hidle, hAt, -⟩ := hG
  obtain ⟨i, hi, hnd⟩ := hex
  by_cases hs : Spins N i l cs[i]
  · obtain ⟨s2, h2, tn, hl2, hw, hlt, -⟩ := hs
    have := replay_eq hl hl2; subst this
    have inv := replay_inv hl
    have htk := inv.tkLt i tn (by simp [hw, Phase.tk])
    obtain ⟨d, hd⟩ := replay_cover hl s.now (Nat.le_refl _) (by omega)
    have hdT : d < cs.length := by
      refine Classical.byContradiction fun hc => ?_
      have hTd : T ≤ d := by rw [← hlen]; exact Nat.le_of_not_lt hc
      rw [hidle d hTd] at hd; simp [Phase.tk] at hd
    refine ⟨d, hdT, fun hdone => ?_, fun ⟨s3, h3, tn', hl3, hw3, hlt3, _⟩ => ?_⟩
    · rw [at_done (hAt d hdT) hdone] at hd; simp [Phase.tk] at hd
    · have := replay_eq hl hl3; subst this
      rw [hw3] at hd; simp [Phase.tk] at hd; omega
  · exact ⟨i, hi, hnd, hs⟩

/-- **The termination certificate of the ticket-lock client** on the C machine. -/
theorem cert (N T : Nat) : LiveCert P (GI N T) (Act N) where
  le hG hS := let ⟨Φ', h1, h2, _⟩ := gstep hG hS; ⟨Φ', h2, h1⟩
  lt hG ha hS := by
    obtain ⟨Φ', h1, _, h3, _⟩ := gstep hG hS
    obtain ⟨hd, _, hns⟩ := ha
    exact ⟨Φ', h3 hd hns, h1⟩
  persist hG ha hS hne := by
    obtain ⟨_, _, _, _, h4⟩ := gstep hG hS
    obtain ⟨hd, hnd, hns⟩ := ha
    obtain ⟨hd', heq⟩ := hS.other hd hne
    exact ⟨hd', by rw [heq]; exact hnd, by rw [heq]; exact fun h => hns (h4 _ (Ne.symm hne) hd h)⟩
  act hG hex := act_exists hG hex
  act_lt _ ha := let ⟨hd, hnd, _⟩ := ha; ⟨hd, hnd⟩

theorem ginit (T N : Nat) (hT : T ≤ NCPU) (hN : N < 2 ^ 32) :
    GI N T (cPool T N) [] (T * (N * 25 + 4)) :=
  ⟨PState.init, [], fun _ => N * 25 + 4, rfl, by simp [cPool], hT, hN, fun _ _ => rfl,
    fun i hi => by simp only [cPool, List.getElem_replicate]; exact .p0 rfl, (sumTo_const _ _).symm⟩

theorem gsteps {N T : Nat} {cs cs' : List (CThread Prim)} {l l' : Log} (h : CSteps P cs l cs' l') :
    ∀ {Φ}, GI N T cs l Φ → ∃ Φ', GI N T cs' l' Φ' := by
  induction h with
  | refl => intro Φ hG; exact ⟨Φ, hG⟩
  | step h₁ _ ih =>
    intro Φ hG
    obtain ⟨i, hi⟩ := h₁.labelled
    obtain ⟨Φ', hG', -⟩ := gstep hG hi
    exact ih hG'

/-! ## Python: the translated client terminates under fair scheduling -/

theorem implBound : ImplBound impl 8 := by
  intro p args x; cases p <;> simp [impl, LoopFree, csize]

theorem prims_total : ∀ i p (args : List ClightL.Expr) (σ : Locals) (a : Log),
    args.length = arity p → ∃ v a', P i p (args.map (·.eval σ)) a = some (v, a') := by
  intro i p args σ a h
  simp only [arity, List.length_eq_zero_iff] at h; subst h
  cases p <;> simp [prims]

/-- **Liveness, in Python.** For `T ≤ NCPU` threads running the translated
client `N` times each: every run in which, within every `K` steps, each
unfinished thread takes a step, has fewer than `11 * K * (T * (25 * N + 4) + 1)`
steps. -/
theorem python_fair_terminates (T N : Nat) (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (r : Run)
    (h0 : r.pool 0 = pyPool T N) (hH : r.heap 0 = H0) {K : Nat} (hK : 0 < K) (hF : r.Fair K) :
    r.len < 11 * K * (T * (N * 25 + 4) + 1) := by
  have hR : Rel impl Rsv arity R (cPool T N) [] (r.pool 0) (r.heap 0) := by
    rw [h0, hH]; exact sync_rel (sync0 T N)
  exact fair_bound primOK implBound (cert N T) r hK hF hR (ginit T N hT hN)

/-- **No deadlock, in Python.** A reachable state with an unfinished thread
can always take a step. -/
theorem python_no_deadlock (T N : Nat) {k : Nat} {ts : Pool} {H : Heap}
    (h : MSteps k (pyPool T N) H0 ts H) (hne : ∃ i, ∃ hi : i < ts.length, ts[i].cmd ≠ .skip) :
    ∃ ts' H', MStep ts H ts' H' := by
  obtain ⟨cs, l, -, hR⟩ := python_refines_c T N h
  exact rel_progress primOK prims_total hR hne

/-- **The final state, in Python.** When every thread has finished,
`lk.ticket == lk.now`: every ticket taken was served. -/
theorem python_final (T N : Nat) (hT : T ≤ NCPU) (hN : N < 2 ^ 32) {k : Nat} {ts : Pool} {H : Heap}
    (h : MSteps k (pyPool T N) H0 ts H) (hdone : ∀ i (hi : i < ts.length), ts[i].cmd = .skip) :
    H tkLoc = H nwLoc := by
  obtain ⟨cs, l, hc, hR⟩ := python_refines_c T N h
  obtain ⟨Φ, s, hs, ws, hl, hlen, -, -, hidle, hAt, -⟩ := gsteps hc (ginit T N hT hN)
  obtain ⟨⟨hRT, hRN⟩, hfin⟩ := py_done hR hdone
  have hall : ∀ d, s.phase d = .idle := by
    intro d
    by_cases hd : d < cs.length
    · have := hfin d hd (hR.len ▸ hd)
      exact at_done (hAt d hd) ⟨this.1, this.2.1⟩
    · have hTd : T ≤ d := by rw [← hlen]; exact Nat.le_of_not_lt hd
      exact hidle d hTd
  have hact : active s = 0 := cnt_zero (fun d => by rw [hall d]; rfl) NCPU
  have hcount := (replay_inv hl).count
  obtain ⟨hn, htk⟩ := replay_counts hl
  rw [hRT, hRN]; congr 2; omega

end TicketLive
