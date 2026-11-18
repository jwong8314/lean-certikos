import CertiKOS.SchedFair

/-!
# Environment fairness for any client with bounded critical sections

`SchedFair.lean` derives CCAL's environment-fairness assumption (`EnvFair`)
from a fair scheduler, for one client program. Here the derivation is generic.

* `OwnerCert r T B`: what a pool of client programs must provide. The global
  log stays valid, non-idle CPUs are unfinished threads, and the **owner
  bound**: while a CPU owns the ticket being served and `now` has not moved,
  it takes at most `B` steps. This is CCAL's condition that a holder releases
  within a bounded number of its own steps ([OSDI16] Invariant 1), stated
  for the owner of the current ticket. It says nothing about the scheduler.
* `owner_persists`: the owner of the current ticket stays its owner until
  `now` moves. This is a fact about the protocol, for any programs.
* `envFair_of_cert`: **any pool with an owner bound `B`, under any `K`-fair
  scheduler, satisfies `EnvFair ((B + 1) * K)`.** The owner exists (the
  tickets cover `now`), fairness gives it `B + 1` steps in `(B + 1) * K`
  machine steps, and the owner bound allows only `B` before `now` moves.
* `ticket_cert`: the ticket-lock client has owner bound 16 (from its
  program-point weights). `fair_envFair_gen` recovers `EnvFair (17 * K)` as
  an instance, and `multicore_acquire_fair_gen` the bounded acquire.
-/

namespace EnvFairGen

open ClightL Ticket ClightToPy TicketPy TicketLive Link LiveLink LiveLink.CRun SchedFair

variable {r : CRun}

/-- What a pool of clients provides: validity, liveness of queued CPUs, and
the owner bound `B`. -/
structure OwnerCert (r : CRun) (T B : Nat) : Prop where
  valid : ∀ j, j ≤ r.len → ∃ s h, replay (r.lg j) = some (s, h)
  len : ∀ j, j ≤ r.len → (r.cs j).length = T
  thread : ∀ j, j ≤ r.len → ∀ s h, replay (r.lg j) = some (s, h) → ∀ d, s.phase d ≠ .idle → d < T
  live : ∀ j, j ≤ r.len → ∀ s h, replay (r.lg j) = some (s, h) → ∀ d (hd : d < (r.cs j).length),
    s.phase d ≠ .idle → ¬ Done (r.cs j)[d]
  bound : ∀ n t d v, n ≤ t → t ≤ r.len →
    (∀ s h, replay (r.lg n) = some (s, h) → (s.phase d).tk = some v) →
    (∀ j, n ≤ j → j ≤ t → now (r.lg j) = v) →
    Ticket.cnt (fun j => decide (n ≤ j ∧ r.lab j = d)) t ≤ B

/-- Events of `d` alone keep `d`'s ticket while `now` does not move. -/
theorem own_events_tk {d : CPU} {v : Nat} : ∀ (ys : Log) {l : Log} {s s' : PState} {h h' : List HEvent},
    (∀ e ∈ ys, e.cpu = d) → replay l = some (s, h) → replay (ys ++ l) = some (s', h') →
    (s.phase d).tk = some v → s'.now = s.now → (s'.phase d).tk = some v
  | [], l, s, s', h, h', _, hl, hr, htk, _ => by
    simp only [List.nil_append] at hr; rw [replay_eq hr hl]; exact htk
  | e :: ys, l, s, s', h, h', hy, hl, hr, htk, hn => by
    obtain ⟨s2, h2, o, hl2, hp, -⟩ := replay_cons hr
    have h1 : s.now ≤ s2.now := by
      have e1 : s.now = now l := (replay_counts hl).1
      have e2 : s2.now = now (ys ++ l) := (replay_counts hl2).1
      have : now l ≤ now (ys ++ l) := by unfold now; rw [countK_append]; omega
      omega
    have h2' := (pstep_now hp).1
    have ih := own_events_tk ys (fun e' he' => hy e' (List.mem_cons_of_mem _ he')) hl hl2 htk (by omega)
    obtain ⟨c, k⟩ := e
    have hc : c = d := hy _ List.mem_cons_self
    subst hc
    exact pstep_own_tk hp ih (by omega)

/-- **The owner stays the owner until `now` moves.** -/
theorem owner_persists (hV : ∀ j, j ≤ r.len → ∃ s h, replay (r.lg j) = some (s, h)) {n t d v : Nat}
    (ht : t ≤ r.len) (htk0 : ∀ s h, replay (r.lg n) = some (s, h) → (s.phase d).tk = some v)
    (hnow : ∀ j, n ≤ j → j ≤ t → now (r.lg j) = v) :
    ∀ k, n + k ≤ t → ∀ s h, replay (r.lg (n + k)) = some (s, h) → (s.phase d).tk = some v := by
  intro k
  induction k with
  | zero => intro _ s h hs; exact htk0 s h hs
  | succ k ih =>
    intro hk s' h' hs'
    obtain ⟨s, h, hs⟩ := hV (n + k) (by omega)
    have htk := ih (by omega) s h hs
    obtain ⟨ys, hys, hy⟩ := lg_ext (r := r) (n := n + k) (by omega)
    rw [← Nat.add_assoc, hys] at hs'
    have hv1 := hnow (n + k) (by omega) (by omega)
    have hv2 := hnow (n + k + 1) (by omega) (by omega)
    have hn1 : s.now = v := by rw [(replay_counts hs).1, hv1]
    have hn2 : s'.now = v := by rw [(replay_counts hs').1, ← hys, hv2]
    by_cases hlab : r.lab (n + k) = d
    · exact own_events_tk ys (fun e he => by rw [hy e he, hlab]) hs hs' htk (by omega)
    · have := (replay_others ys (fun e he => by rw [hy e he]; exact hlab) hs hs').1
      rw [this]; exact htk

/-- **Environment fairness from an owner bound and a fair scheduler.** -/
theorem envFair_of_cert {T B K : Nat} (hC : OwnerCert r T B) (hF : Fair r K) (c : CPU) :
    r.EnvFair c ((B + 1) * K) := by
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
  obtain ⟨g, hg, hlg⟩ := hC.valid n hnl
  have hgc : g.phase c = s.phase c := by
    rw [hxs] at hlg; exact (replay_others xs hx hs hlg).1
  have hgn : g.now = v := by rw [(replay_counts hlg).1, hnow n (Nat.le_refl _) (by omega)]
  have hsn : s.now = v := (replay_counts hs).1
  have hi := replay_inv hlg
  have htk : tn < g.ticket := hi.tkLt c tn (by rw [hgc, hw]; rfl)
  obtain ⟨d, hd⟩ := replay_cover hlg v (by omega) (by omega)
  have htk0 : ∀ s' h', replay (r.lg n) = some (s', h') → (s'.phase d).tk = some v :=
    fun s' h' hs' => by rw [replay_eq hs' hlg]; exact hd
  have hown := owner_persists (r := r) hC.valid ht htk0 hnow
  let gc : Nat → Bool := fun j => decide (n ≤ j ∧ r.lab j = d)
  have hg0 : Ticket.cnt gc n = 0 := by
    rw [cnt_congr (g' := fun _ => false) n (fun j hj => by simp [gc]; omega)]
    exact cnt_zero (fun _ => rfl) n
  -- fairness: the owner moves in each of `B + 1` windows
  have hcount : ∀ i, i ≤ B + 1 → i ≤ Ticket.cnt gc (n + i * K) := by
    intro i
    induction i with
    | zero => intro _; simp [hg0]
    | succ i ih =>
      intro hi'
      have ih' := ih (by omega)
      have hA_le : n + i * K + K ≤ t := by
        have : (i + 1) * K ≤ (B + 1) * K := Nat.mul_le_mul_right K hi'
        rw [Nat.succ_mul] at this; omega
      obtain ⟨s1, h1, hl1⟩ := hC.valid (n + i * K) (by omega)
      have htk1 := hown (i * K) (by omega) s1 h1 hl1
      have hne : s1.phase d ≠ .idle := fun e => by rw [e] at htk1; simp [Phase.tk] at htk1
      have hdT := hC.thread (n + i * K) (by omega) s1 h1 hl1 d hne
      have hdj : d < (r.cs (n + i * K)).length := by rw [hC.len _ (by omega)]; exact hdT
      have hnd := hC.live (n + i * K) (by omega) s1 h1 hl1 d hdj hne
      obtain ⟨j, hj1, hj2, hj3⟩ := hF (n + i * K) (by omega) d hdj hnd
      have hgj : gc j = true := by simp [gc, hj3]; omega
      have e1 : Ticket.cnt gc (n + i * K) ≤ Ticket.cnt gc j := cnt_mono hj1
      have e2 : Ticket.cnt gc (j + 1) ≤ Ticket.cnt gc (n + (i + 1) * K) :=
        cnt_mono (by rw [Nat.succ_mul]; omega)
      have e3 : Ticket.cnt gc (j + 1) = Ticket.cnt gc j + 1 := by simp [Ticket.cnt, hgj]
      omega
  have hB := hcount (B + 1) (Nat.le_refl _)
  have hcnt : B + 1 ≤ Ticket.cnt gc t := Nat.le_trans hB (cnt_mono (by omega))
  have hb : Ticket.cnt gc t ≤ B := hC.bound n t d v (by omega) ht htk0 hnow
  omega

/-! ## The ticket-lock client as an instance -/

theorem ticket_owner_steps {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (h0 : r.cs 0 = cPool T N)
    (hl0 : r.lg 0 = []) {n t d v : Nat} (hnt : n ≤ t)
    (ht : t ≤ r.len) (hdT : d < T)
    (htk0 : ∀ s h, replay (r.lg n) = some (s, h) → (s.phase d).tk = some v)
    (hnow : ∀ j, n ≤ j → j ≤ t → now (r.lg j) = v) :
    Ticket.cnt (fun j => decide (n ≤ j ∧ r.lab j = d)) t ≤ 16 := by
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
  -- the weight lives in a band of width 15
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
  show Ticket.cnt g t ≤ 16
  omega

/-- The ticket-lock client has owner bound 16. -/
theorem ticket_cert {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (h0 : r.cs 0 = cPool T N)
    (hl0 : r.lg 0 = []) : OwnerCert r T 16 where
  valid := fun j hj => by
    obtain ⟨Φ, s, h, ws, hl, -⟩ := run_gi hT hN h0 hl0 hj; exact ⟨s, h, hl⟩
  len := fun j hj => by
    obtain ⟨Φ, s, h, ws, -, hlen, -⟩ := run_gi hT hN h0 hl0 hj; exact hlen
  thread := fun j hj s h hs d hne => by
    obtain ⟨Φ, g, hg, ws, hlg, hlen, -, -, hidle, -, -⟩ := run_gi hT hN h0 hl0 hj
    rw [replay_eq hs hlg] at hne
    exact Nat.lt_of_not_le fun hge => hne (hidle d hge)
  live := fun j hj s h hs d hd hne hdone => by
    obtain ⟨Φ, g, hg, ws, hlg, hlen, -, -, -, hAt, -⟩ := run_gi hT hN h0 hl0 hj
    rw [replay_eq hs hlg] at hne
    exact hne (at_done (hAt d hd) hdone)
  bound := fun n t d v hnt ht htk0 hnow => by
    obtain ⟨s, h, ws, hl⟩ : ∃ s h, ∃ _ : Nat → Nat, replay (r.lg n) = some (s, h) := by
      obtain ⟨Φ, s, h, ws, hl, -⟩ := run_gi hT hN h0 hl0 (j := n) (by omega); exact ⟨s, h, ws, hl⟩
    have hne : s.phase d ≠ .idle := fun e => by
      have := htk0 s h hl; rw [e] at this; simp [Phase.tk] at this
    have hdT : d < T := by
      obtain ⟨Φ, g, hg, ws', hlg, hlen, -, -, hidle, -, -⟩ := run_gi hT hN h0 hl0 (j := n) (by omega)
      rw [replay_eq hl hlg] at hne
      exact Nat.lt_of_not_le fun hge => hne (hidle d hge)
    exact ticket_owner_steps hT hN h0 hl0 hnt ht hdT htk0 hnow

/-- `SchedFair.fair_envFair`, as an instance of the generic theorem. -/
theorem fair_envFair_gen {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (h0 : r.cs 0 = cPool T N)
    (hl0 : r.lg 0 = []) {K : Nat} (hF : Fair r K) (c : CPU) : r.EnvFair c (17 * K) :=
  envFair_of_cert (ticket_cert hT hN h0 hl0) hF c

/-- Bounded acquire under a fair scheduler, through the generic theorem. -/
theorem multicore_acquire_fair_gen {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (r : CRun)
    (h0 : r.cs 0 = cPool T N) (hl0 : r.lg 0 = []) {K : Nat} (hF : Fair r K) {c : CPU} (hc : c < T)
    {a t : Nat} {σ : Locals} (hat : a ≤ t) (ht : t ≤ r.len)
    (ha : (r.cs a)[c]? = some ⟨acquireCode, KA N, σ⟩)
    (hhold : cntC c .hold (r.lg t) = cntC c .hold (r.lg a)) :
    cntC c .getNow (r.lg t) ≤ cntC c .getNow (r.lg a) + (NCPU + 1) * (17 * K + 2) + 1 :=
  multicore_acquire_bounded hT hN r h0 hl0 hc (fair_envFair_gen hT hN h0 hl0 hF c) hat ht ha hhold

end EnvFairGen
