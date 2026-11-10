import CertiKOS.LiveLink

/-!
# Environment fairness from a fair scheduler

`LiveLink.multicore_acquire_bounded` assumes `EnvFair D`: whenever CPU `c`
polls while it is not its turn, `now` advances within `D` steps of the
multicore machine. CCAL also takes this as an assumption about the
environment. Here it is *derived*, for the ticket-lock client, from scheduler
fairness alone.

* `CRun.Fair K`: in every window of `K` steps, every unfinished CPU moves.
* `owner_window`: suppose `now` stays fixed at `v` for `17 * K` steps. The CPU
  `d` owning ticket `v` (it exists by `Cover`) is never spinning. So each of
  its steps lowers its program-point weight (`own_step`) and nobody else's
  step raises it (`at_other`). Fairness gives it 17 steps, but while it owns
  the current ticket its weight stays in a band of width 15
  (`at_owner`: `(N - m - 1) * 25 + [6, 21]` within iteration `m`, and `m` is
  fixed because its `i` is untouched, `own_i`). Contradiction.
* `fair_envFair`: hence `EnvFair (17 * K)`.
* `multicore_acquire_fair`: under a `K`-fair scheduler, each acquire on the
  multicore machine polls at most `(NCPU + 1) * (17 * K + 2) + 1` times. This
  is the per-CPU `acquire_live_bounded`, now with no fairness assumption
  beyond the scheduler's.
-/

namespace SchedFair

open ClightL Ticket ClightToPy TicketPy TicketLive Link LiveLink LiveLink.CRun

/-! ## Facts about one CPU's steps -/

theorem step_locals {Pn Abs : Type} {P : Prims Pn Abs} {t : CThread Pn} {a : Abs} {y : Config Pn Abs}
    (hs : ClightL.step P (t.cfg a) = some y) :
    y.locals = t.locals ∨ (∃ z e, t.stmt = .assign z e ∧ y.locals = t.locals.set z (e.eval t.locals)) ∨
      (∃ z p args v, t.stmt = .call z p args ∧ y.locals = t.locals.set z v) := by
  obtain ⟨s, k, σ⟩ := t
  cases s with
  | skip =>
    left
    cases k <;> simp only [ClightL.step, CThread.cfg, Option.some.injEq, reduceCtorEq] at hs <;>
      subst hs <;> rfl
  | assign z e =>
    right; left; simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hs; subst hs
    exact ⟨z, e, rfl, rfl⟩
  | seq => left; simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hs; subst hs; rfl
  | ite => left; simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hs; subst hs; rfl
  | «while» e b =>
    left
    rw [cstep_while] at hs
    by_cases he : e.eval σ = 0
    · rw [if_pos he, Option.some.injEq] at hs; subst hs; rfl
    · rw [if_neg he, Option.some.injEq] at hs; subst hs; rfl
  | call z p args =>
    right; right
    simp only [ClightL.step, CThread.cfg] at hs
    split at hs
    · rename_i v a' _
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨z, p, args, v, rfl, rfl⟩
    · simp at hs

/-- Outside the idle points, the client never writes its loop counter `i`. -/
theorem own_i {N : Nat} {d : CPU} {s : PState} {t : CThread Prim} {w : Nat} {l : Log}
    {c' : Config Prim Log} (hA : At N d s t w) (hph : s.phase d ≠ .idle)
    (hst : ClightL.step (prims noEnv d) (t.cfg l) = some c') : c'.locals "i" = t.locals "i" := by
  rcases step_locals hst with h | ⟨z, e, hz, h⟩ | ⟨z, p, args, v, hz, h⟩
  · rw [h]
  · exfalso
    cases hA <;> simp_all [KT, KW, KH, KL, KA, KR, KO, gnC, holdCall, releaseCode, acquireLoop,
      acquireCode, incI, bodyS, loopS, clientCode]
  · rw [h]
    have hz' : z ≠ "i" := by
      cases hA <;> simp only [gnC, holdCall, releaseCode, acquireCode, acquireLoop, incI, bodyS,
        loopS, clientCode, Stmt.call.injEq, reduceCtorEq] at hz <;>
        first | (obtain ⟨rfl, -⟩ := hz; decide) | (exact absurd ‹_ = Phase.idle› hph)
    exact Locals.set_other _ _ (Ne.symm hz')

/-- While a CPU holds a ticket, its weight lies in one band of its iteration. -/
theorem at_owner {N : Nat} {d : CPU} {s : PState} {t : CThread Prim} {w : Nat} (hA : At N d s t w)
    (hph : s.phase d ≠ .idle) :
    ∃ m, m < N ∧ t.locals "i" = BitVec.ofNat 32 m ∧ (N - m - 1) * 25 + 6 ≤ w ∧
      w ≤ (N - m - 1) * 25 + 21 := by
  cases hA <;> first | (exfalso; simp_all; done) | skip
  all_goals
    obtain ⟨hm, hi⟩ := ‹Iter N _ _›
    refine ⟨_, hm, hi, ?_, ?_⟩ <;> (try unfold w12) <;> (try unfold w13) <;> (try unfold w14) <;>
      (repeat' split) <;> omega

theorem pstep_own_tk {s s' : PState} {d : CPU} {k : EvKind} {o : Option HEvent} {v : Nat}
    (hp : pstep s ⟨d, k⟩ = some (s', o)) (htk : (s.phase d).tk = some v) (hn : s'.now = s.now) :
    (s'.phase d).tk = some v := by
  simp only [pstep] at hp
  split at hp
  case isFalse => simp at hp
  cases k <;> cases hph : s.phase d <;> simp only [hph] at hp htk <;> simp [Phase.tk] at htk <;>
    (try simp at hp)
  all_goals first
    | (obtain ⟨rfl, -⟩ := hp; simp at hn; done)
    | (obtain ⟨-, rfl, -⟩ := hp; simp [Phase.tk, htk]; done)
    | (obtain ⟨rfl, -⟩ := hp; simp [hph, Phase.tk, htk])

theorem at_others_le {N : Nat} {c : CPU} {t : CThread Prim} :
    ∀ (xs : Log) {l : Log} {s s' : PState} {h h' : List HEvent} {w : Nat},
      (∀ e ∈ xs, e.cpu ≠ c) → replay l = some (s, h) → replay (xs ++ l) = some (s', h') →
      At N c s t w → ∃ w', w' ≤ w ∧ At N c s' t w'
  | [], l, s, s', h, h', w, _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨w, Nat.le_refl _, hA⟩
  | e :: xs, l, s, s', h, h', w, hx, hl, hr, hA => by
    obtain ⟨s2, h2, o, hl2, hp, -⟩ := replay_cons hr
    obtain ⟨w2, hw2, hA2⟩ :=
      at_others_le xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA
    obtain ⟨w', hw', hA'⟩ := at_other (replay_inv hl2) hp (hx e List.mem_cons_self) hA2
    exact ⟨w', by omega, hA'⟩

theorem cnt_mono {g : Nat → Bool} : ∀ {a b : Nat}, a ≤ b → Ticket.cnt g a ≤ Ticket.cnt g b := by
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with h | h
    · have := ih (by omega); simp only [Ticket.cnt]; omega
    · subst h; exact Nat.le_refl _

theorem ofNat_inj {a b N : Nat} (ha : a < N) (hb : b < N) (hN : N < 2 ^ 32)
    (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-! ## Runs: fairness, and what every reachable state satisfies -/


variable (r : CRun)

/-- **Scheduler fairness.** In every window of `K` steps, every unfinished CPU moves. -/
def Fair (K : Nat) : Prop :=
  ∀ n, n + K ≤ r.len → ∀ d (hd : d < (r.cs n).length), ¬ Done (r.cs n)[d] →
    ∃ j, n ≤ j ∧ j < n + K ∧ r.lab j = d

variable {r}

theorem lg_suffix : ∀ {n m : Nat}, n ≤ m → m ≤ r.len → ∃ zs, r.lg m = zs ++ r.lg n := by
  intro n m hnm hm
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact ⟨[], rfl⟩
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with h | h
    · obtain ⟨zs, hzs⟩ := ih (by omega) (by omega)
      obtain ⟨ys, hys, -⟩ := lg_ext (r := r) (n := m) (by omega)
      exact ⟨ys ++ zs, by rw [hys, hzs, List.append_assoc]⟩
    · subst h; exact ⟨[], rfl⟩

theorem now_mono {n m : Nat} (hnm : n ≤ m) (hm : m ≤ r.len) : now (r.lg n) ≤ now (r.lg m) := by
  obtain ⟨zs, hzs⟩ := lg_suffix (r := r) hnm hm
  rw [hzs]; unfold now; rw [countK_append]; omega

theorem run_gi {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (h0 : r.cs 0 = cPool T N)
    (hl0 : r.lg 0 = []) {j : Nat} (hj : j ≤ r.len) : ∃ Φ, GI N T (r.cs j) (r.lg j) Φ := by
  have := run_csteps (r := r) j hj
  rw [h0, hl0] at this
  exact gsteps this (ginit T N hT hN)

/-! ## The owner of the current ticket makes progress -/

theorem owner_window {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (h0 : r.cs 0 = cPool T N)
    (hl0 : r.lg 0 = []) {K : Nat} (hF : Fair r K) {n t d v : Nat} (hnt : n + 17 * K ≤ t)
    (ht : t ≤ r.len) (hdT : d < T)
    (htk0 : ∀ s h, replay (r.lg n) = some (s, h) → (s.phase d).tk = some v)
    (hnow : ∀ j, n ≤ j → j ≤ t → now (r.lg j) = v) : False := by
  have hdN : d < NCPU := Nat.lt_of_lt_of_le hdT hT
  have hlenT : ∀ j, j ≤ r.len → (r.cs j).length = T := fun j hj => by
    obtain ⟨Φ, s, h, ws, -, hlen, -⟩ := run_gi hT hN h0 hl0 hj; exact hlen
  let g : Nat → Bool := fun j => decide (n ≤ j ∧ r.lab j = d)
  have hg0 : Ticket.cnt g n = 0 := by
    rw [cnt_congr (g' := fun _ => false) n (fun j hj => by simp [g]; omega)]
    exact cnt_zero (fun _ => rfl) n
  -- the starting weight
  obtain ⟨Φ0, s0, h0', ws, hl0', hlen0, -, -, -, hAt0, -⟩ := run_gi hT hN h0 hl0 (j := n) (by omega)
  have hdn : d < (r.cs n).length := by rw [hlen0]; exact hdT
  let w0 := ws d
  let σi := (r.cs n)[d].locals "i"
  -- the invariant along the window
  let Q : Nat → Prop := fun j => ∃ s h w, replay (r.lg j) = some (s, h) ∧
    ∃ hdj : d < (r.cs j).length, At N d s (r.cs j)[d] w ∧ w + Ticket.cnt g j ≤ w0 ∧
      (s.phase d).tk = some v ∧ (r.cs j)[d].locals "i" = σi
  have hQ : ∀ k, n + k ≤ t → Q (n + k) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨s0, h0', w0, hl0', hdn, hAt0 d hdn, by simp [hg0], htk0 _ _ hl0', rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, h, w, hl, hdj, hA, hw, htk, hi⟩ := ih (by omega)
      have hjl : n + k < r.len := by omega
      have hv1 := hnow (n + k) (by omega) (by omega)
      have hv2 := hnow (n + k + 1) (by omega) (by omega)
      have hsn : s.now = v := by rw [(replay_counts hl).1, hv1]
      have hph : s.phase d ≠ .idle := fun e => by rw [e] at htk; simp [Phase.tk] at htk
      obtain ⟨hi', c', hst, hcs, hlg⟩ := r.step (n + k) hjl
      obtain ⟨Φ1, s1, h1, ws1, hl1, -⟩ := run_gi hT hN h0 hl0 (j := n + k + 1) (by omega)
      have hs1n : s1.now = v := by rw [(replay_counts hl1).1, hv2]
      have hdj' : d < (r.cs (n + k + 1)).length := by rw [hlenT _ (by omega)]; exact hdT
      rw [← Nat.add_assoc]
      by_cases hlab : r.lab (n + k) = d
      · -- the owner moves: its weight drops
        have hst' : ClightL.step (prims noEnv d) ((r.cs (n + k))[d].cfg (r.lg (n + k))) = some c' := by
          subst hlab; exact hst
        obtain ⟨s', hlog, w', hA', hdec⟩ := own_step hdN hN hl hA hst'
        have hrep' : ∃ h', replay (r.lg (n + k + 1)) = some (s', h') := by
          rcases hlog with ⟨he, rfl⟩ | ⟨kk, o, he, hp⟩
          · rw [hlg, he]; exact ⟨_, hl⟩
          · rw [hlg, he]; exact ⟨_, replay_cons_of hl hp⟩
        obtain ⟨hh', hrep⟩ := hrep'
        have hss : s' = s1 := replay_eq hrep hl1
        have htk' : (s'.phase d).tk = some v := by
          rcases hlog with ⟨-, rfl⟩ | ⟨kk, o, he, hp⟩
          · exact htk
          · exact pstep_own_tk hp htk (by rw [hss, hs1n, hsn])
        have hwl : w' < w := by
          rcases hdec with h | ⟨-, s2, h2, tn, hl2, hph2, hlt2, -⟩
          · exact h
          · exfalso
            rw [replay_eq hl2 hl] at hph2 hlt2
            rw [hph2] at htk; simp [Phase.tk] at htk; omega
        have hcd : (r.cs (n + k + 1))[d] = thr c' := by
          simp only [hcs, hlab, List.getElem_set_self]
        have hg1 : Ticket.cnt g (n + k + 1) = Ticket.cnt g (n + k) + 1 := by
          simp [Ticket.cnt, g, hlab]
        refine ⟨s', _, w', hrep, hdj', hcd ▸ hA', by omega, htk', ?_⟩
        rw [hcd]; show c'.locals "i" = σi
        rw [own_i hA hph hst', hi]
      · -- another CPU moves: the owner's weight does not rise
        obtain ⟨ys, hys, hy⟩ := gstep_log hst
        have hcd : (r.cs (n + k + 1))[d] = (r.cs (n + k))[d] := by
          simp only [hcs]; rw [List.getElem_set_ne hlab]
        have hl1' : replay (ys ++ r.lg (n + k)) = some (s1, h1) := by rw [← hys, ← hlg]; exact hl1
        have hx : ∀ e ∈ ys, e.cpu ≠ d := fun e he => by rw [hy e he]; exact hlab
        obtain ⟨w', hw', hA'⟩ := at_others_le ys hx hl hl1' hA
        have hph' := (replay_others ys hx hl hl1').1
        have hg1 : Ticket.cnt g (n + k + 1) = Ticket.cnt g (n + k) := by
          simp [Ticket.cnt, g, hlab]
        refine ⟨s1, h1, w', hl1, hdj', hcd ▸ hA', by omega, by rw [hph']; exact htk, ?_⟩
        rw [hcd]; exact hi
  -- fairness: the owner moves in each of 17 windows
  have hcount : ∀ i, i ≤ 17 → i ≤ Ticket.cnt g (n + i * K) := by
    intro i
    induction i with
    | zero => intro _; simp [hg0]
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hA_le : n + i * K + K ≤ t := by
        have : (i + 1) * K ≤ 17 * K := Nat.mul_le_mul_right K hi
        rw [Nat.succ_mul] at this; omega
      obtain ⟨s, h, w, hl, hdj, hA, -, htk, -⟩ := hQ (i * K) (by omega)
      have hnd : ¬ Done (r.cs (n + i * K))[d] := fun hd => by
        rw [at_done hA hd] at htk; simp [Phase.tk] at htk
      obtain ⟨j, hj1, hj2, hj3⟩ := hF (n + i * K) (by omega) d hdj hnd
      have hgj : g j = true := by simp [g, hj3]; omega
      have e1 : Ticket.cnt g (n + i * K) ≤ Ticket.cnt g j := cnt_mono hj1
      have e2 : Ticket.cnt g (j + 1) ≤ Ticket.cnt g (n + (i + 1) * K) :=
        cnt_mono (by rw [Nat.succ_mul]; omega)
      have e3 : Ticket.cnt g (j + 1) = Ticket.cnt g j + 1 := by simp [Ticket.cnt, hgj]
      omega
  have h17 := hcount 17 (Nat.le_refl _)
  have hcnt : 17 ≤ Ticket.cnt g t := Nat.le_trans h17 (cnt_mono (by omega))
  -- but the weight lives in a band of width 15
  have hQt := hQ (t - n) (by omega)
  rw [show n + (t - n) = t by omega] at hQt
  obtain ⟨s, h, wt, hl, hdt, hAt, hwt, htk, hit⟩ := hQt
  have hph : s.phase d ≠ .idle := fun e => by rw [e] at htk; simp [Phase.tk] at htk
  have hph0 : s0.phase d ≠ .idle := fun e => by
    have := htk0 _ _ hl0'; rw [e] at this; simp [Phase.tk] at this
  obtain ⟨m0, hm0, hi0, -, hw0⟩ := at_owner (hAt0 d hdn) hph0
  obtain ⟨mt, hmt, hiT, hwT, -⟩ := at_owner hAt hph
  have hmm : mt = m0 := ofNat_inj hmt hm0 hN (by rw [← hiT, ← hi0]; exact hit)
  subst hmm
  have : wt + 17 ≤ w0 := by omega
  omega

/-! ## `EnvFair` from scheduler fairness -/

theorem fair_envFair {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (h0 : r.cs 0 = cPool T N)
    (hl0 : r.lg 0 = []) {K : Nat} (hF : Fair r K) (c : CPU) : r.EnvFair c (17 * K) := by
  intro n hn s h tn hs hw hlt t hnt ht
  apply Classical.byContradiction
  intro hle
  have hnl : n ≤ r.len := Nat.le_of_lt hn.1
  let v := now (r.vw c n)
  obtain ⟨xs, hxs, hx⟩ := vw_split (r := r) (c := c) n hnl
  have hvn : now (r.lg n) = now xs + v := by rw [hxs]; unfold now; rw [countK_append]; rfl
  have hnow : ∀ j, n ≤ j → j ≤ t → now (r.lg j) = v := by
    intro j h1 h2
    have := now_mono (r := r) h1 (by omega)
    have := now_mono (r := r) h2 ht
    omega
  obtain ⟨Φ, g, hg, ws, hlg, hlen, -, -, hidle, -, -⟩ := run_gi hT hN h0 hl0 hnl
  have hgc : g.phase c = s.phase c := by
    rw [hxs] at hlg; exact (replay_others xs hx hs hlg).1
  have hgn : g.now = v := by rw [(replay_counts hlg).1, hnow n (Nat.le_refl _) (by omega)]
  have hsn : s.now = v := (replay_counts hs).1
  have hi := replay_inv hlg
  have htk : tn < g.ticket := hi.tkLt c tn (by rw [hgc, hw]; rfl)
  obtain ⟨d, hd⟩ := replay_cover hlg v (by omega) (by omega)
  have hdT : d < T := Nat.lt_of_not_le fun hge => by rw [hidle d hge] at hd; simp [Phase.tk] at hd
  exact owner_window hT hN h0 hl0 hF hnt ht hdT
    (fun s' h' hs' => by rw [replay_eq hs' hlg]; exact hd) hnow

/-- **Bounded acquire on the multicore machine, under a fair scheduler only.**
In any run of T ≤ NCPU CPUs running the client under a `K`-fair scheduler,
once CPU `c` starts `acquire`, it polls `now` at most
`(NCPU + 1) * (17 * K + 2) + 1` times before its `hold`. -/
theorem multicore_acquire_fair {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (r : CRun)
    (h0 : r.cs 0 = cPool T N) (hl0 : r.lg 0 = []) {K : Nat} (hF : Fair r K) {c : CPU} (hc : c < T)
    {a t : Nat} {σ : Locals} (hat : a ≤ t) (ht : t ≤ r.len)
    (ha : (r.cs a)[c]? = some ⟨acquireCode, KA N, σ⟩)
    (hhold : cntC c .hold (r.lg t) = cntC c .hold (r.lg a)) :
    cntC c .getNow (r.lg t) ≤ cntC c .getNow (r.lg a) + (NCPU + 1) * (17 * K + 2) + 1 :=
  multicore_acquire_bounded hT hN r h0 hl0 hc (fair_envFair hT hN h0 hl0 hF c) hat ht ha hhold

end SchedFair
