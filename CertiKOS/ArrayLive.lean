import CertiKOS.NoLostUpdate
import CertiKOS.FairC

/-!
# Liveness of the lock array on the multicore machine

The client of `NoLostUpdate.lean` (each CPU: `acquire(L c); v = v + 1;
release(L c)`, CPUs may share locks), run by any scheduler that moves every
unfinished CPU within every `K` steps, terminates: `array_fair_terminates`
bounds every such run by `K * (27 * T + 1)` steps.

* `AtW`: the program points with a weight, the steps left. The three
  wait-loop points weigh 19 while it is not the CPU's turn, so spinning does
  not lower the weight.
* `own_stepW`: a CPU's step lowers its weight unless it is spinning.
  `at_otherW`: another CPU's event never raises it.
* The potential is the sum of the weights. Per lock, the CPU whose ticket is
  being served (it exists by `Cover`) is never spinning. So while any CPU is
  unfinished, some CPU is active (`act_exists`). This is the certificate
  `certA`, and `FairC.fair_terminates` turns it into the bound.
-/

namespace ArrayLive

open ClightL Ticket ClightToPy LockArray LinkA TicketLive ArrayLinkClient NoLostUpdate FairC

def wq8 (p : PState) (tn : Nat) (σ : Locals) : Nat :=
  if p.now = tn then (if σ "n" = σ "t" then 14 else 17) else 19
def wq9 (p : PState) (tn : Nat) : Nat := if p.now = tn then 16 else 19
def wq10 (p : PState) (tn : Nat) (σ : Locals) : Nat :=
  if p.now = tn then (if σ "n" = σ "t" then 15 else 18) else 19

/-- CPU `c` on lock `iv` is at a program point consistent with `p`, with weight `w`. -/
inductive AtW (iv : Val) (c : CPU) (p : PState) : CThread APrim → Nat → Prop
  | q0 {σ} : σ "lk" = iv → p.phase c = .idle → AtW iv c p ⟨code2, .stop, σ⟩ 27
  | q1 {σ} : σ "lk" = iv → p.phase c = .idle → AtW iv c p ⟨acquireA, KR2, σ⟩ 26
  | q2 {σ} : σ "lk" = iv → p.phase c = .idle → AtW iv c p ⟨.call "t" .faiTicket [lkE], .seq restS KR2, σ⟩ 25
  | q3 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW iv c p ⟨.skip, .seq restS KR2, σ⟩ 24
  | q4 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW iv c p ⟨restS, KR2, σ⟩ 23
  | q5 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW iv c p ⟨gnA, .seq (.seq loopA holdPullS) KR2, σ⟩ 22
  | q6 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn →
      AtW iv c p ⟨.skip, .seq (.seq loopA holdPullS) KR2, σ⟩ 21
  | q7 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtW iv c p ⟨.seq loopA holdPullS, KR2, σ⟩ 20
  | q8 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn →
      AtW iv c p ⟨loopA, .seq holdPullS KR2, σ⟩ (wq8 p tn σ)
  | q9 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW iv c p ⟨gnA, KL2, σ⟩ (wq9 p tn)
  | q10 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtW iv c p ⟨.skip, KL2, σ⟩ (wq10 p tn σ)
  | q11 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtW iv c p ⟨.skip, .seq holdPullS KR2, σ⟩ 13
  | q12 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtW iv c p ⟨holdPullS, KR2, σ⟩ 12
  | q13 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn →
      AtW iv c p ⟨.call "_" .hold [lkE], .seq (.call "v" .pull [lkE]) KR2, σ⟩ 11
  | q14 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtW iv c p ⟨.skip, .seq (.call "v" .pull [lkE]) KR2, σ⟩ 10
  | q15 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW iv c p ⟨.call "v" .pull [lkE], KR2, σ⟩ 9
  | q16 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW iv c p ⟨.skip, KR2, σ⟩ 8
  | r0 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW iv c p ⟨.seq incV releaseA, .stop, σ⟩ 7
  | r1 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW iv c p ⟨incV, .seq releaseA .stop, σ⟩ 6
  | r2 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW iv c p ⟨.skip, .seq releaseA .stop, σ⟩ 5
  | q17 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW iv c p ⟨releaseA, .stop, σ⟩ 4
  | q18 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtW iv c p ⟨.call "_" .push [lkE, .var "v"], .seq (.call "_" .incNow [lkE]) .stop, σ⟩ 3
  | q19 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtW iv c p ⟨.skip, .seq (.call "_" .incNow [lkE]) .stop, σ⟩ 2
  | q20 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW iv c p ⟨.call "_" .incNow [lkE], .stop, σ⟩ 1
  | done {σ} : σ "lk" = iv → p.phase c = .idle → AtW iv c p ⟨.skip, .stop, σ⟩ 0

/-- The three points of the wait loop. -/
def InLoopW (t : CThread APrim) : Prop :=
  (t.stmt = loopA ∧ t.cont = .seq holdPullS KR2) ∨ t.cont = KL2

theorem wq_le (p : PState) (tn : Nat) (σ : Locals) : wq8 p tn σ ≤ 19 ∧ wq9 p tn ≤ 19 ∧ wq10 p tn σ ≤ 19 := by
  unfold wq8 wq9 wq10; refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> omega

theorem at_otherW {iv : Val} {c : CPU} {p p' : PState} {e : Event} {o : Option HEvent}
    {t : CThread APrim} {w : Nat} (hi : Inv p) (hp : pstep p e = some (p', o)) (hne : e.cpu ≠ c)
    (hA : AtW iv c p t w) : ∃ w', w' ≤ w ∧ AtW iv c p' t w' := by
  have hph : p'.phase c = p.phase c := (pstep_other hp hne).1
  have hnow : p.now ≤ p'.now := (pstep_now hp).1
  have hW : ∀ {σ tn}, Wt c p σ tn → Wt c p' σ tn := fun hw => ⟨by rw [hph]; exact hw.1, hw.2⟩
  have hN : ∀ {σ tn}, NInv σ p tn → NInv σ p' tn := fun ⟨v, h1, h2, h3⟩ => ⟨v, by omega, h2, h3⟩
  have hS : ∀ {σ tn}, Wt c p σ tn → p.now = tn → p'.now = tn := fun hw hn =>
    now_stays hi hp hne hw.1 hn
  have hI : p.phase c = .idle → p'.phase c = .idle := fun h => by rw [hph]; exact h
  have hH : ∀ {tn}, p.phase c = .holding tn → p'.phase c = .holding tn := fun h => by rw [hph]; exact h
  have mono : ∀ {σ tn}, Wt c p σ tn → wq8 p' tn σ ≤ wq8 p tn σ ∧ wq9 p' tn ≤ wq9 p tn ∧
      wq10 p' tn σ ≤ wq10 p tn σ := by
    intro σ tn hw
    by_cases h1 : p.now = tn
    · simp [wq8, wq9, wq10, h1, hS hw h1]
    · have := wq_le p' tn σ
      have e8 : wq8 p tn σ = 19 := by simp [wq8, h1]
      have e9 : wq9 p tn = 19 := by simp [wq9, h1]
      have e10 : wq10 p tn σ = 19 := by simp [wq10, h1]
      rw [e8, e9, e10]; exact this
  cases hA with
  | q0 hk h => exact ⟨_, Nat.le_refl _, .q0 hk (hI h)⟩
  | q1 hk h => exact ⟨_, Nat.le_refl _, .q1 hk (hI h)⟩
  | q2 hk h => exact ⟨_, Nat.le_refl _, .q2 hk (hI h)⟩
  | q3 hk hw => exact ⟨_, Nat.le_refl _, .q3 hk (hW hw)⟩
  | q4 hk hw => exact ⟨_, Nat.le_refl _, .q4 hk (hW hw)⟩
  | q5 hk hw => exact ⟨_, Nat.le_refl _, .q5 hk (hW hw)⟩
  | q6 hk hw hn => exact ⟨_, Nat.le_refl _, .q6 hk (hW hw) (hN hn)⟩
  | q7 hk hw hn => exact ⟨_, Nat.le_refl _, .q7 hk (hW hw) (hN hn)⟩
  | q8 hk hw hn => exact ⟨_, (mono hw).1, .q8 hk (hW hw) (hN hn)⟩
  | q9 hk hw => exact ⟨_, (mono hw).2.1, .q9 hk (hW hw)⟩
  | q10 hk hw hn => exact ⟨_, (mono hw).2.2, .q10 hk (hW hw) (hN hn)⟩
  | q11 hk hw h => exact ⟨_, Nat.le_refl _, .q11 hk (hW hw) (hS hw h)⟩
  | q12 hk hw h => exact ⟨_, Nat.le_refl _, .q12 hk (hW hw) (hS hw h)⟩
  | q13 hk hw h => exact ⟨_, Nat.le_refl _, .q13 hk (hW hw) (hS hw h)⟩
  | q14 hk h => exact ⟨_, Nat.le_refl _, .q14 hk (hH h)⟩
  | q15 hk h => exact ⟨_, Nat.le_refl _, .q15 hk (hH h)⟩
  | q16 hk h => exact ⟨_, Nat.le_refl _, .q16 hk (hH h)⟩
  | r0 hk h => exact ⟨_, Nat.le_refl _, .r0 hk (hH h)⟩
  | r1 hk h => exact ⟨_, Nat.le_refl _, .r1 hk (hH h)⟩
  | r2 hk h => exact ⟨_, Nat.le_refl _, .r2 hk (hH h)⟩
  | q17 hk h => exact ⟨_, Nat.le_refl _, .q17 hk (hH h)⟩
  | q18 hk h => exact ⟨_, Nat.le_refl _, .q18 hk (hH h)⟩
  | q19 hk h => exact ⟨_, Nat.le_refl _, .q19 hk (hH h)⟩
  | q20 hk h => exact ⟨_, Nat.le_refl _, .q20 hk (hH h)⟩
  | done hk h => exact ⟨_, Nat.le_refl _, .done hk (hI h)⟩

theorem at_othersW {iv : Val} {c : CPU} {t : CThread APrim} :
    ∀ (xs : ALog) {l : ALog} {S S' : AState} {H H' : HLogA} {w : Nat},
      (∀ e ∈ xs, e.cpu ≠ c) → areplay l = some (S, H) → areplay (xs ++ l) = some (S', H') →
      AtW iv c (S.lk iv.toNat) t w → ∃ w', w' ≤ w ∧ AtW iv c (S'.lk iv.toNat) t w'
  | [], l, S, S', H, H', w, _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨w, Nat.le_refl _, hA⟩
  | e :: xs, l, S, S', H, H', w, hx, hl, hr, hA => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := areplay_cons hr
    obtain ⟨w2, hw2, hA2⟩ := at_othersW xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA
    rcases astep_lkA hp iv.toNat with h | ⟨k, o', hps⟩
    · rw [h]; exact ⟨w2, hw2, hA2⟩
    · obtain ⟨w', hw', hA'⟩ :=
        at_otherW (replay_inv (areplay_proj hl2 iv.toNat)) hps (hx e List.mem_cons_self) hA2
      exact ⟨w', by omega, hA'⟩

/-! ## Our own step -/

def OutW (iv : Val) (c : CPU) (l : ALog) (S : AState) (t : CThread APrim) (w : Nat)
    (c' : Config APrim ALog) : Prop :=
  ∃ S' H' w', areplay c'.abs = some (S', H') ∧ AtW iv c (S'.lk iv.toNat) (thr c') w' ∧
    (w' < w ∨ (w' = w ∧ ∃ tn, (S.lk iv.toNat).phase c = .waiting tn ∧ (S.lk iv.toNat).now < tn ∧ InLoopW t)) ∧
    ∃ ys, c'.abs = ys ++ l ∧ ∀ e ∈ ys, e.cpu = c ∧ e.lk = iv.toNat

theorem wout_nonev {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {w w' : Nat} {c' : Config APrim ALog} (hl : areplay l = some (S, H)) (habs : c'.abs = l)
    (hA : AtW iv c (S.lk iv.toNat) (thr c') w')
    (hd : w' < w ∨ (w' = w ∧ ∃ tn, (S.lk iv.toNat).phase c = .waiting tn ∧ (S.lk iv.toNat).now < tn ∧ InLoopW t)) :
    OutW iv c l S t w c' :=
  ⟨S, H, w', habs ▸ hl, hA, hd, [], by simp [habs], by simp⟩

theorem wout_tk {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {w w' : Nat} {c' : Config APrim ALog} {k : EvKind} {p' : PState} {o : Option HEvent}
    (hl : areplay l = some (S, H)) (hps : pstep (S.lk iv.toNat) ⟨c, k⟩ = some (p', o))
    (habs : c'.abs = ev c iv.toNat k :: l) (hA : AtW iv c p' (thr c') w')
    (hd : w' < w ∨ (w' = w ∧ ∃ tn, (S.lk iv.toNat).phase c = .waiting tn ∧ (S.lk iv.toNat).now < tn ∧ InLoopW t)) :
    OutW iv c l S t w c' :=
  ⟨_, _, w', habs ▸ areplay_cons_of hl (astep_tk hps), by simpa using hA, hd, [ev c iv.toNat k], habs,
    by simp [ev]⟩

theorem wout_nolk {iv : Val} {c : CPU} {l : ALog} {S S' : AState} {H : HLogA} {t : CThread APrim}
    {w w' : Nat} {c' : Config APrim ALog} {k : AKind} (hl : areplay l = some (S, H))
    (hps : astep S ⟨c, iv.toNat, k⟩ = some (S', none)) (hlk : S'.lk = S.lk)
    (habs : c'.abs = ⟨c, iv.toNat, k⟩ :: l) (hA : AtW iv c (S.lk iv.toNat) (thr c') w') (hlt : w' < w) :
    OutW iv c l S t w c' :=
  ⟨_, _, w', habs ▸ areplay_cons_of hl hps, by rw [hlk]; exact hA, .inl hlt, [⟨c, iv.toNat, k⟩], habs,
    by simp⟩

theorem own_stepW {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {w : Nat} {c' : Config APrim ALog} (hc : c < NCPU) (hl : areplay l = some (S, H))
    (hA : AtW iv c (S.lk iv.toNat) t w)
    (hst : ClightL.step (aprims noEnvA c) (t.cfg l) = some c') : OutW iv c l S t w c' := by
  have hpr := areplay_proj hl iv.toNat
  have hi := replay_inv hpr
  obtain ⟨hn, htk⟩ := replay_counts hpr
  cases hA with
  | q0 hk hp =>
    simp only [ClightL.step, CThread.cfg, code2, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q1 hk hp) (.inl (by omega))
  | q1 hk hp =>
    simp only [ClightL.step, CThread.cfg, acquireA_eq, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q2 hk hp) (.inl (by omega))
  | @q2 σ hk hp =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incTicket⟩ = some (⟨(S.lk iv.toNat).ticket + 1,
        (S.lk iv.toNat).now, setPhase (S.lk iv.toNat).phase c (.waiting (S.lk iv.toNat).ticket)⟩, none) := by
      simp [pstep, hc, hp]
    exact wout_tk hl hps rfl (.q3 (tn := (S.lk iv.toNat).ticket) (by simp [hk]) ⟨by simp, by simp [htk]⟩)
      (.inl (by omega))
  | q3 hk hw =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q4 hk hw) (.inl (by omega))
  | q4 hk hw =>
    simp only [ClightL.step, CThread.cfg, restS, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q5 hk hw) (.inl (by omega))
  | @q5 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine wout_tk hl hps rfl (.q6 (tn := tn) (by simp [hk]) ⟨hw.1, by simp [hw.2]⟩ ?_) (.inl (by omega))
    rw [← hn]; exact nInv_fresh hi hw.1 σ
  | q6 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q7 hk hw hni) (.inl (by omega))
  | @q7 σ tn hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q8 hk hw hni) (.inl (Nat.lt_of_le_of_lt (wq_le _ _ _).1 (by decide)))
  | @q8 σ tn hk hw hni =>
    change ClightL.step _ (CThread.cfg ⟨.while lgEA gnA, .seq holdPullS KR2, σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    by_cases hz : lgEA.eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have heq : σ "n" = σ "t" := by rw [lgEA, ne_eval_zero] at hz; simpa [Expr.eval] using hz
      have hnow := nInv_exit hi hw hni heq
      exact wout_nonev hl rfl (.q11 hk hw hnow) (.inl (by simp [wq8, hnow, heq]))
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      have hne : ¬ σ "n" = σ "t" := by
        intro h; apply hz; rw [lgEA, ne_eval_zero]; simpa [Expr.eval] using h
      refine wout_nonev hl rfl (.q9 hk hw) ?_
      by_cases hnow : (S.lk iv.toNat).now = tn
      · left; simp [wq8, wq9, hnow, hne]
      · right; refine ⟨by simp [wq8, wq9, hnow], tn, hw.1, ?_, .inl ⟨rfl, rfl⟩⟩
        have := hi.waitGe c tn hw.1; omega
  | @q9 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine wout_tk hl hps rfl (.q10 (tn := tn) (by simp [hk]) ⟨hw.1, by simp [hw.2]⟩
      (by rw [← hn]; exact nInv_fresh hi hw.1 σ)) ?_
    by_cases hnow : (S.lk iv.toNat).now = tn
    · left
      have e2 : BitVec.ofNat 32 (now (projL iv.toNat l)) = σ "t" := by rw [hw.2, ← hn, hnow]
      simp [wq9, wq10, hnow, e2]
    · right; refine ⟨by simp [wq9, wq10, hnow], tn, hw.1, ?_, .inr rfl⟩
      have := hi.waitGe c tn hw.1; omega
  | @q10 σ tn hk hw hni =>
    simp only [ClightL.step, CThread.cfg, KL2, Option.some.injEq] at hst; subst hst
    refine wout_nonev hl rfl (.q8 hk hw hni) ?_
    by_cases hnow : (S.lk iv.toNat).now = tn
    · left; simp only [wq8, wq10, hnow, ite_true]; split <;> omega
    · right; refine ⟨by simp [wq8, wq10, hnow], tn, hw.1, ?_, .inr rfl⟩
      have := hi.waitGe c tn hw.1; omega
  | q11 hk hw h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q12 hk hw h) (.inl (by omega))
  | q12 hk hw h =>
    simp only [ClightL.step, CThread.cfg, holdPullS, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q13 hk hw h) (.inl (by omega))
  | @q13 σ tn hk hw h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .hold⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now,
        setPhase (S.lk iv.toNat).phase c (.holding tn)⟩, some (.acq c)) := by
      simp [pstep, hc, hw.1, h]
    exact wout_tk hl hps rfl (.q14 (tn := tn) (by simp [hk]) (by simp)) (.inl (by omega))
  | q14 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q15 hk h) (.inl (by omega))
  | @q15 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    exact wout_nolk hl (by simp [astep, Holding, h]) rfl rfl (.q16 (tn := tn) (by simp [hk]) h) (by omega)
  | q16 hk h =>
    simp only [ClightL.step, CThread.cfg, KR2, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.r0 hk h) (.inl (by omega))
  | r0 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.r1 hk h) (.inl (by omega))
  | @r1 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, incV, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.r2 (tn := tn) (by simp [hk]) h) (.inl (by omega))
  | r2 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q17 hk h) (.inl (by omega))
  | q17 hk h =>
    simp only [ClightL.step, CThread.cfg, releaseA_eq, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q18 hk h) (.inl (by omega))
  | @q18 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    exact wout_nolk (S' := ⟨S.lk, upd S.mem iv.toNat (σ "v"), upd S.dirty iv.toNat true⟩) hl
      (by simp [astep, Holding, h]) rfl rfl (.q19 (tn := tn) (by simp [hk]) h) (by omega)
  | q19 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q20 hk h) (.inl (by omega))
  | @q20 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incNow⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now + 1,
        setPhase (S.lk iv.toNat).phase c .idle⟩, some (.rel c)) := by
      simp [pstep, hc, h]
    exact wout_tk hl hps rfl (.done (by simp [hk]) (by simp)) (.inl (by omega))
  | done hk h => simp [ClightL.step, CThread.cfg] at hst

/-! ## Facts about the global log -/

/-- CPUs that never act stay idle on every lock. -/
theorem idle_beyond {T : Nat} : ∀ {l : ALog} {S : AState} {H : HLogA}, (∀ e ∈ l, e.cpu < T) →
    areplay l = some (S, H) → ∀ d, T ≤ d → ∀ j, (S.lk j).phase d = .idle
  | [], S, H, _, hr, d, _, j => by simp [areplay] at hr; obtain ⟨rfl, -⟩ := hr; rfl
  | e :: l, S', H', hev, hr, d, hd, j => by
    obtain ⟨S, H, o, hl, hp, -⟩ := areplay_cons hr
    have ih := idle_beyond (fun e' he' => hev e' (List.mem_cons_of_mem _ he')) hl d hd j
    have hne : e.cpu ≠ d := Nat.ne_of_lt (Nat.lt_of_lt_of_le (hev e List.mem_cons_self) hd)
    rcases astep_lkA hp j with h | ⟨k, o', hps⟩
    · rw [h]; exact ih
    · rw [(pstep_other hps hne).1]; exact ih

theorem now_ext {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) :
    ∀ (ys : ALog) {S' : AState} {H' : HLogA}, areplay (ys ++ l) = some (S', H') →
      ∀ j, (S.lk j).now ≤ (S'.lk j).now
  | [], S', H', hr, j => by simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact Nat.le_refl _
  | e :: ys, S', H', hr, j => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := areplay_cons hr
    have ih := now_ext hl ys hl2 j
    rcases astep_lkA hp j with h | ⟨k, o', hps⟩
    · rw [h]; exact ih
    · exact Nat.le_trans ih (pstep_now hps).1

theorem lk_frame {i : Nat} {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) :
    ∀ (ys : ALog), (∀ e ∈ ys, e.lk = i) → ∀ {S' : AState} {H' : HLogA}, areplay (ys ++ l) = some (S', H') →
      ∀ j, j ≠ i → S'.lk j = S.lk j
  | [], _, S', H', hr, j, _ => by simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; rfl
  | e :: ys, hy, S', H', hr, j, hj => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := areplay_cons hr
    have ih := lk_frame hl ys (fun e' he' => hy e' (List.mem_cons_of_mem _ he')) hl2 j hj
    rw [← ih]
    obtain ⟨d, j', k⟩ := e
    have hj' : j' = i := hy _ List.mem_cons_self
    cases k with
    | tk k =>
      simp only [astep] at hp
      split at hp
      · simp at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        simp [LockArray.upd, hj', hj]
    | pull =>
      simp only [astep] at hp; split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl
      · simp at hp
    | push v =>
      simp only [astep] at hp; split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl
      · simp at hp

theorem atW_done {iv : Val} {c : CPU} {p : PState} {t : CThread APrim} {w : Nat} (hA : AtW iv c p t w)
    (hd : Done t) : p.phase c = .idle := by
  obtain ⟨h1, h2⟩ := hd
  cases hA <;> simp_all [KR2, KL2, code2, incV, acquireA, releaseA, restS, gnA, holdPullS, loopA, lgEA]

/-! ## The global potential -/

def GL (T : Nat) (L : Nat → Val) (cs : List (CThread APrim)) (l : ALog) (Φ : Nat) : Prop :=
  ∃ S H, ∃ ws : Nat → Nat, areplay l = some (S, H) ∧ cs.length = T ∧ T ≤ NCPU ∧ (∀ e ∈ l, e.cpu < T) ∧
    (∀ c (hc : c < cs.length), AtW (L c) c (S.lk (L c).toNat) cs[c] (ws c)) ∧
    (∀ c, c < T → ∀ j, j ≠ (L c).toNat → (S.lk j).phase c = .idle) ∧ Φ = sumTo ws T

def SpinsW (L : Nat → Val) (cs : List (CThread APrim)) (l : ALog) (d : Nat) : Prop :=
  ∃ (hd : d < cs.length) (S : AState) (H : HLogA) (tn : Nat), areplay l = some (S, H) ∧
    (S.lk (L d).toNat).phase d = .waiting tn ∧ (S.lk (L d).toNat).now < tn ∧ InLoopW cs[d]

def ActW (L : Nat → Val) (cs : List (CThread APrim)) (l : ALog) (d : Nat) : Prop :=
  ∃ hd : d < cs.length, ¬ Done cs[d] ∧ ¬ SpinsW L cs l d

theorem gstepW {T : Nat} {L : Nat → Val} {cs cs' : List (CThread APrim)} {l l' : ALog} {Φ a : Nat}
    (hG : GL T L cs l Φ) (hS : CStepI PGA a cs l cs' l') :
    ∃ Φ', GL T L cs' l' Φ' ∧ Φ' ≤ Φ ∧ (¬ SpinsW L cs l a → Φ' < Φ) ∧
      (∀ d, d ≠ a → SpinsW L cs' l' d → SpinsW L cs l d) := by
  obtain ⟨S, H, ws, hl, hlen, hT, hev, hAt, hidle, rfl⟩ := hG
  obtain ⟨ha, c', hst, rfl, rfl⟩ := hS
  have haT : a < T := hlen ▸ ha
  have haN : a < NCPU := Nat.lt_of_lt_of_le haT hT
  obtain ⟨S', H', w', hr', hA', hdec, ys, hys, hown⟩ := own_stepW haN hl (hAt a ha) hst
  have hr'' : areplay (ys ++ l) = some (S', H') := hys ▸ hr'
  have hx : ∀ d, d ≠ a → ∀ e ∈ ys, e.cpu ≠ d := fun d hd e he => by rw [(hown e he).1]; exact Ne.symm hd
  -- the other CPUs' new weights
  have hch : ∀ d, ∃ w'', ∀ hd : d < cs.length, d ≠ a → w'' ≤ ws d ∧
      AtW (L d) d (S'.lk (L d).toNat) cs[d] w'' := by
    intro d
    by_cases hd : d < cs.length
    · by_cases hda : d = a
      · exact ⟨0, fun _ h => absurd hda h⟩
      · obtain ⟨w'', h1, h2⟩ := at_othersW ys (hx d hda) hl hr'' (hAt d hd)
        exact ⟨w'', fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hd⟩
  let ws' : Nat → Nat := fun d => if d = a then w' else Classical.choose (hch d)
  have hws' : ∀ d (hd : d < cs.length), d ≠ a → ws' d ≤ ws d ∧ AtW (L d) d (S'.lk (L d).toNat) cs[d] (ws' d) :=
    fun d hd hda => by simp only [ws', hda, ite_false]; exact Classical.choose_spec (hch d) hd hda
  have hwa : ws' a = w' := by simp [ws']
  have hle : ∀ d, d < T → ws' d ≤ ws d := fun d hd => by
    by_cases hda : d = a
    · subst hda; rw [hwa]; rcases hdec with h | ⟨h, -⟩ <;> omega
    · exact (hws' d (hlen ▸ hd) hda).1
  refine ⟨sumTo ws' T, ⟨S', H', ws', hr', by simpa using hlen, hT, fun e he => ?_, fun c hc => ?_,
    fun c hc j hj => ?_, rfl⟩, sumTo_le T hle, fun hns => ?_, fun d hda hsp => ?_⟩
  · rw [hys] at he
    rcases List.mem_append.1 he with he | he
    · rw [(hown e he).1]; exact haT
    · exact hev e he
  · by_cases hca : c = a
    · subst hca; simp only [List.getElem_set_self]; rw [hwa]; simpa using hA'
    · have hc' : c < cs.length := by simpa using hc
      simp only [List.getElem_set_ne (Ne.symm hca)]
      exact (hws' c hc' hca).2
  · by_cases hca : c = a
    · subst hca
      rw [lk_frame hl ys (fun e he => (hown e he).2) hr'' j hj]
      exact hidle c hc j hj
    · rw [(others_events ys (hx c hca) hl hr'').1 j]
      exact hidle c hc j hj
  · refine sumTo_lt (i := a) T hle haT ?_
    rw [hwa]
    rcases hdec with h | ⟨-, tn, h1, h2, h3⟩
    · exact h
    · exact absurd ⟨ha, S, H, tn, hl, h1, h2, h3⟩ hns
  · obtain ⟨hd', S2, H2, tn, hl2, h1, h2, h3⟩ := hsp
    rw [hr'] at hl2; cases hl2
    have hd : d < cs.length := by simpa using hd'
    have hph := (others_events ys (hx d hda) hl hr'').1 (L d).toNat
    have hnow := now_ext hl ys hr'' (L d).toNat
    refine ⟨hd, S, H, tn, hl, by rw [← hph]; exact h1, by omega, ?_⟩
    simpa [List.getElem_set_ne (Ne.symm hda)] using h3

theorem act_existsW {T : Nat} {L : Nat → Val} {cs : List (CThread APrim)} {l : ALog} {Φ : Nat}
    (hG : GL T L cs l Φ) (hu : ∃ i, ∃ hi : i < cs.length, ¬ Done cs[i]) : ∃ d, ActW L cs l d := by
  refine Classical.byContradiction fun hno => ?_
  have hall : ∀ d (hd : d < cs.length), ¬ Done cs[d] → SpinsW L cs l d := fun d hd hnd =>
    Classical.byContradiction fun hs => hno ⟨d, hd, hnd, hs⟩
  obtain ⟨S, H, ws, hl, hlen, hT, hev, hAt, hidle, -⟩ := hG
  obtain ⟨i, hi, hnd⟩ := hu
  obtain ⟨-, S2, H2, tn, hl2, hw, hlt, -⟩ := hall i hi hnd
  rw [hl] at hl2; cases hl2
  -- the owner of the ticket being served on that lock
  obtain ⟨k, hk⟩ : ∃ k, k = (L i).toNat := ⟨_, rfl⟩
  rw [← hk] at hw hlt
  have hp := areplay_proj hl k
  have hinv := replay_inv hp
  have htk := hinv.tkLt i tn (by simp [hw, Phase.tk])
  obtain ⟨d, hd⟩ := replay_cover hp (S.lk k).now (Nat.le_refl _) (by omega)
  have hdT : d < T := Nat.lt_of_not_le fun hge => by
    rw [idle_beyond hev hl d hge k] at hd; simp [Phase.tk] at hd
  have hkd : k = (L d).toNat := Classical.byContradiction fun hne => by
    rw [hidle d hdT k hne] at hd; simp [Phase.tk] at hd
  have hd' : d < cs.length := by rw [hlen]; exact hdT
  have hndd : ¬ Done cs[d] := fun hdn => by
    have := atW_done (hAt d hd') hdn
    rw [← hkd] at this; rw [this] at hd; simp [Phase.tk] at hd
  obtain ⟨-, S3, H3, tn', hl3, hw', hlt', -⟩ := hall d hd' hndd
  rw [hl] at hl3; cases hl3
  rw [← hkd] at hw' hlt'
  rw [hw'] at hd; simp [Phase.tk] at hd; omega

theorem certA (T : Nat) (L : Nat → Val) : LiveCert PGA (GL T L) (ActW L) where
  le := fun hG hS => let ⟨Φ', h1, h2, _, _⟩ := gstepW hG hS; ⟨Φ', h2, h1⟩
  lt := fun hG hA hS => by
    obtain ⟨Φ', h1, -, h3, -⟩ := gstepW hG hS
    obtain ⟨_, _, hns⟩ := hA
    exact ⟨Φ', h3 hns, h1⟩
  persist := fun {cs a Φ i d cs' a'} hG hA hS hid => by
    obtain ⟨-, -, -, -, hsp⟩ := gstepW hG hS
    obtain ⟨hd, hnd, hns⟩ := hA
    obtain ⟨hd', hcs⟩ := hS.other hd hid
    exact ⟨hd', by rw [hcs]; exact hnd, fun h => hns (hsp d (Ne.symm hid) h)⟩
  act := fun hG hu => act_existsW hG hu
  act_lt := fun _ hA => let ⟨hd, hnd, _⟩ := hA; ⟨hd, hnd⟩

theorem gl_init (T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) : GL T L (poolD T L) [] (T * 27) := by
  refine ⟨_, _, fun _ => 27, rfl, by simp [poolD], hT, by simp, fun c hc => ?_, fun c _ j _ => rfl,
    (sumTo_const _ _).symm⟩
  simp only [poolD, List.getElem_map, List.getElem_range]
  exact .q0 (by simp) rfl

/-- **Liveness of the lock array on the multicore machine.** Every run of
`T ≤ NCPU` CPUs running `acquire(L c); v = v + 1; release(L c)` in which every
unfinished CPU moves within every `K` steps has fewer than `K * (27 * T + 1)`
steps. -/
theorem array_fair_terminates (T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) (r : GRun PGA)
    (h0 : r.cs 0 = poolD T L) (hl0 : r.ab 0 = []) {K : Nat} (hK : 0 < K) (hF : r.Fair K) :
    r.len < K * (T * 27 + 1) :=
  fair_terminates (certA T L) r hK (by rw [h0, hl0]; exact gl_init T L hT) hF

end ArrayLive
