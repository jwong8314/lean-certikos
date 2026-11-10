import CertiKOS.LinkA
import CertiKOS.TicketLive

/-!
# The lock array on the multicore machine, from the per-CPU proofs

The instance of `LinkA.lean`. Each CPU `c` runs `acquire(lk); release(lk)` on
its own choice of lock `L c` (CPUs may share locks). Its correctness on the
multicore machine is derived only from per-CPU reasoning.

* `AtA`: the 23 program points of `acquireA; releaseA`, each tied to the
  protocol state of the CPU's lock. Safety only, so no weights: the per-CPU
  guarantee must hold under *every* rely-respecting environment, fair or not.
* `own_stepA` (a step of the CPU) and `at_otherA` (another CPU's event)
  preserve it. `client_guarA`: the per-CPU guarantee `GuarA`.
* `array_linked`: every multicore run is explained by the per-CPU layers, and
  the global array log is valid (all locks' protocols, block ownership).
* `multicore_cs_exclusiveA`: two CPUs inside their critical sections on the
  same lock are the same CPU.
-/

namespace ArrayLinkClient

open ClightL Ticket ClightToPy LockArray LinkA TicketLive

/-! ## The program points -/

def holdPullS : Stmt APrim := .seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE])
def lgEA : Expr := .bin .ne (.var "n") (.var "t")
def gnA : Stmt APrim := .call "n" .getNow [lkE]
def restS : Stmt APrim := .seq gnA (.seq loopA holdPullS)
def KR : Cont APrim := .seq releaseA .stop
def KLA : Cont APrim := .loop lgEA gnA (.seq holdPullS KR)
def code : Stmt APrim := .seq acquireA releaseA

theorem acquireA_eq : acquireA = .seq (.call "t" .faiTicket [lkE]) restS := rfl
theorem loopA_eq : loopA = .while lgEA gnA := rfl
theorem releaseA_eq : releaseA = .seq (.call "_" .push [lkE, .var "v"]) (.call "_" .incNow [lkE]) := rfl

/-- CPU `c`, working on lock `iv`, is at a program point consistent with that
lock's protocol state `p`. -/
inductive AtA (iv : Val) (c : CPU) (p : PState) : CThread APrim → Prop
  | q0 {σ} : σ "lk" = iv → p.phase c = .idle → AtA iv c p ⟨code, .stop, σ⟩
  | q1 {σ} : σ "lk" = iv → p.phase c = .idle → AtA iv c p ⟨acquireA, KR, σ⟩
  | q2 {σ} : σ "lk" = iv → p.phase c = .idle → AtA iv c p ⟨.call "t" .faiTicket [lkE], .seq restS KR, σ⟩
  | q3 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtA iv c p ⟨.skip, .seq restS KR, σ⟩
  | q4 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtA iv c p ⟨restS, KR, σ⟩
  | q5 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtA iv c p ⟨gnA, .seq (.seq loopA holdPullS) KR, σ⟩
  | q6 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn →
      AtA iv c p ⟨.skip, .seq (.seq loopA holdPullS) KR, σ⟩
  | q7 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtA iv c p ⟨.seq loopA holdPullS, KR, σ⟩
  | q8 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtA iv c p ⟨loopA, .seq holdPullS KR, σ⟩
  | q9 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtA iv c p ⟨gnA, KLA, σ⟩
  | q10 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtA iv c p ⟨.skip, KLA, σ⟩
  | q11 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtA iv c p ⟨.skip, .seq holdPullS KR, σ⟩
  | q12 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtA iv c p ⟨holdPullS, KR, σ⟩
  | q13 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn →
      AtA iv c p ⟨.call "_" .hold [lkE], .seq (.call "v" .pull [lkE]) KR, σ⟩
  | q14 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtA iv c p ⟨.skip, .seq (.call "v" .pull [lkE]) KR, σ⟩
  | q15 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtA iv c p ⟨.call "v" .pull [lkE], KR, σ⟩
  | q16 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtA iv c p ⟨.skip, KR, σ⟩
  | q17 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtA iv c p ⟨releaseA, .stop, σ⟩
  | q18 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtA iv c p ⟨.call "_" .push [lkE, .var "v"], .seq (.call "_" .incNow [lkE]) .stop, σ⟩
  | q19 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtA iv c p ⟨.skip, .seq (.call "_" .incNow [lkE]) .stop, σ⟩
  | q20 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtA iv c p ⟨.call "_" .incNow [lkE], .stop, σ⟩
  | done {σ} : σ "lk" = iv → p.phase c = .idle → AtA iv c p ⟨.skip, .stop, σ⟩

/-! ## Another CPU's event -/

theorem at_otherA {iv : Val} {c : CPU} {p p' : PState} {e : Event} {o : Option HEvent}
    {t : CThread APrim} (hi : Inv p) (hp : pstep p e = some (p', o)) (hne : e.cpu ≠ c)
    (hA : AtA iv c p t) : AtA iv c p' t := by
  have hph : p'.phase c = p.phase c := (pstep_other hp hne).1
  have hnow : p.now ≤ p'.now := (pstep_now hp).1
  have hW : ∀ {σ tn}, Wt c p σ tn → Wt c p' σ tn := fun hw => ⟨by rw [hph]; exact hw.1, hw.2⟩
  have hN : ∀ {σ tn}, NInv σ p tn → NInv σ p' tn := fun ⟨v, h1, h2, h3⟩ => ⟨v, by omega, h2, h3⟩
  have hS : ∀ {σ tn}, Wt c p σ tn → p.now = tn → p'.now = tn := fun hw hn =>
    now_stays hi hp hne hw.1 hn
  have hI : p.phase c = .idle → p'.phase c = .idle := fun h => by rw [hph]; exact h
  have hH : ∀ {tn}, p.phase c = .holding tn → p'.phase c = .holding tn := fun h => by rw [hph]; exact h
  cases hA with
  | q0 hk h => exact .q0 hk (hI h)
  | q1 hk h => exact .q1 hk (hI h)
  | q2 hk h => exact .q2 hk (hI h)
  | q3 hk hw => exact .q3 hk (hW hw)
  | q4 hk hw => exact .q4 hk (hW hw)
  | q5 hk hw => exact .q5 hk (hW hw)
  | q6 hk hw hn => exact .q6 hk (hW hw) (hN hn)
  | q7 hk hw hn => exact .q7 hk (hW hw) (hN hn)
  | q8 hk hw hn => exact .q8 hk (hW hw) (hN hn)
  | q9 hk hw => exact .q9 hk (hW hw)
  | q10 hk hw hn => exact .q10 hk (hW hw) (hN hn)
  | q11 hk hw h => exact .q11 hk (hW hw) (hS hw h)
  | q12 hk hw h => exact .q12 hk (hW hw) (hS hw h)
  | q13 hk hw h => exact .q13 hk (hW hw) (hS hw h)
  | q14 hk h => exact .q14 hk (hH h)
  | q15 hk h => exact .q15 hk (hH h)
  | q16 hk h => exact .q16 hk (hH h)
  | q17 hk h => exact .q17 hk (hH h)
  | q18 hk h => exact .q18 hk (hH h)
  | q19 hk h => exact .q19 hk (hH h)
  | q20 hk h => exact .q20 hk (hH h)
  | done hk h => exact .done hk (hI h)

/-- An array event of another CPU changes lock `i`'s state by at most one
single-lock protocol step of that CPU. -/
theorem astep_lkA {S S' : AState} {e : AEvent} {o : Option HEventA} (hp : astep S e = some (S', o))
    (i : Nat) : S'.lk i = S.lk i ∨ ∃ k o', pstep (S.lk i) ⟨e.cpu, k⟩ = some (S'.lk i, o') := by
  obtain ⟨d, j, k⟩ := e
  cases k with
  | tk k =>
    simp only [astep] at hp
    split at hp
    · simp at hp
    · rename_i p' o' hps
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      by_cases hji : j = i
      · subst hji; exact .inr ⟨k, o', by simpa using hps⟩
      · exact .inl (by simp [LockArray.upd, Ne.symm hji])
  | pull =>
    simp only [astep] at hp; split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact .inl rfl
    · simp at hp
  | push v =>
    simp only [astep] at hp; split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact .inl rfl
    · simp at hp

theorem at_othersA {iv : Val} {c : CPU} {t : CThread APrim} :
    ∀ (xs : ALog) {l : ALog} {S S' : AState} {H H' : HLogA},
      (∀ e ∈ xs, e.cpu ≠ c) → areplay l = some (S, H) → areplay (xs ++ l) = some (S', H') →
      AtA iv c (S.lk iv.toNat) t → AtA iv c (S'.lk iv.toNat) t
  | [], l, S, S', H, H', _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact hA
  | e :: xs, l, S, S', H, H', hx, hl, hr, hA => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := areplay_cons hr
    have hA2 := at_othersA xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA
    rcases astep_lkA hp iv.toNat with h | ⟨k, o', hps⟩
    · rw [h]; exact hA2
    · exact at_otherA (replay_inv (areplay_proj hl2 iv.toNat)) hps (hx e List.mem_cons_self) hA2

theorem at_pullA {iv : Val} {ε : AEnv} {c : CPU} (hR : RelyA ε c) {l : ALog} {S : AState}
    {H : HLogA} {t : CThread APrim} (hl : areplay l = some (S, H)) (hA : AtA iv c (S.lk iv.toNat) t) :
    ∃ S' H', areplay (apull ε c l) = some (S', H') ∧ AtA iv c (S'.lk iv.toNat) t := by
  obtain ⟨S', H', hr⟩ := hR.conform l S H hl
  exact ⟨S', H', hr, at_othersA (ε.query c l) (ε.noSelf c l) hl hr hA⟩

/-! ## Our own step -/

theorem own_stepA {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {c' : Config APrim ALog} (hc : c < NCPU) (hl : areplay l = some (S, H))
    (hA : AtA iv c (S.lk iv.toNat) t) (hst : ClightL.step (aprims noEnvA c) (t.cfg l) = some c') :
    (c'.abs = l ∧ AtA iv c (S.lk iv.toNat) (thr c')) ∨
      ∃ S' H', areplay c'.abs = some (S', H') ∧ AtA iv c (S'.lk iv.toNat) (thr c') := by
  have hpr := areplay_proj hl iv.toNat
  have hi := replay_inv hpr
  obtain ⟨hn, htk⟩ := replay_counts hpr
  cases hA with
  | q0 hk hp =>
    simp only [ClightL.step, CThread.cfg, code, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q1 hk hp⟩
  | q1 hk hp =>
    simp only [ClightL.step, CThread.cfg, acquireA_eq, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q2 hk hp⟩
  | @q2 σ hk hp =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incTicket⟩ = some (⟨(S.lk iv.toNat).ticket + 1,
        (S.lk iv.toNat).now, setPhase (S.lk iv.toNat).phase c (.waiting (S.lk iv.toNat).ticket)⟩, none) := by
      simp [pstep, hc, hp]
    refine .inr ⟨_, _, areplay_cons_of hl (astep_tk hps), ?_⟩
    exact .q3 (tn := (S.lk iv.toNat).ticket) (by simp [hk]) ⟨by simp, by simp [htk]⟩
  | q3 hk hw =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q4 hk hw⟩
  | q4 hk hw =>
    simp only [ClightL.step, CThread.cfg, restS, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q5 hk hw⟩
  | @q5 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine .inr ⟨_, _, areplay_cons_of hl (astep_tk hps), ?_⟩
    refine .q6 (tn := tn) (by simp [hk]) ⟨by simp [hw.1], by simp [hw.2]⟩ ?_
    simp only [LockArray.upd_same]; rw [← hn]; exact nInv_fresh hi hw.1 σ
  | q6 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q7 hk hw hni⟩
  | q7 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q8 hk hw hni⟩
  | @q8 σ tn hk hw hni =>
    change ClightL.step _ (CThread.cfg ⟨.while lgEA gnA, .seq holdPullS KR, σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    by_cases hz : lgEA.eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have heq : σ "n" = σ "t" := by rw [lgEA, ne_eval_zero] at hz; simpa [Expr.eval] using hz
      exact .inl ⟨rfl, .q11 hk hw (nInv_exit hi hw hni heq)⟩
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      exact .inl ⟨rfl, .q9 hk hw⟩
  | @q9 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine .inr ⟨_, _, areplay_cons_of hl (astep_tk hps), ?_⟩
    refine .q10 (tn := tn) (by simp [hk]) ⟨by simp [hw.1], by simp [hw.2]⟩ ?_
    simp only [LockArray.upd_same]; rw [← hn]; exact nInv_fresh hi hw.1 σ
  | q10 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, KLA, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q8 hk hw hni⟩
  | q11 hk hw h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q12 hk hw h⟩
  | q12 hk hw h =>
    simp only [ClightL.step, CThread.cfg, holdPullS, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q13 hk hw h⟩
  | @q13 σ tn hk hw h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .hold⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now,
        setPhase (S.lk iv.toNat).phase c (.holding tn)⟩, some (.acq c)) := by
      simp [pstep, hc, hw.1, h]
    refine .inr ⟨_, _, areplay_cons_of hl (astep_tk hps), ?_⟩
    exact .q14 (tn := tn) (by simp [hk]) (by simp)
  | q14 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q15 hk h⟩
  | @q15 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hpl : astep S ⟨c, iv.toNat, .pull⟩ = some (S, none) := by simp [astep, Holding, h]
    refine .inr ⟨_, _, areplay_cons_of hl hpl, ?_⟩
    exact .q16 (tn := tn) (by simp [hk]) h
  | q16 hk h =>
    simp only [ClightL.step, CThread.cfg, KR, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q17 hk h⟩
  | q17 hk h =>
    simp only [ClightL.step, CThread.cfg, releaseA_eq, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q18 hk h⟩
  | @q18 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hpu : astep S ⟨c, iv.toNat, .push (σ "v")⟩ =
        some (⟨S.lk, upd S.mem iv.toNat (σ "v"), upd S.dirty iv.toNat true⟩, none) := by
      simp [astep, Holding, h]
    refine .inr ⟨_, _, areplay_cons_of hl hpu, ?_⟩
    exact .q19 (tn := tn) (by simp [hk]) h
  | q19 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact .inl ⟨rfl, .q20 hk h⟩
  | @q20 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incNow⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now + 1,
        setPhase (S.lk iv.toNat).phase c .idle⟩, some (.rel c)) := by
      simp [pstep, hc, h]
    refine .inr ⟨_, _, areplay_cons_of hl (astep_tk hps), ?_⟩
    exact .done (by simp [hk]) (by simp)
  | done hk h => simp [ClightL.step, CThread.cfg] at hst

/-! ## The per-CPU guarantee -/

def PInvA (iv : Val) (ε : AEnv) (c : CPU) (x : Config APrim ALog) : Prop :=
  (∃ S H, areplay x.abs = some (S, H)) ∧
    ∃ S H, areplay (apull ε c x.abs) = some (S, H) ∧ AtA iv c (S.lk iv.toNat) (thr x)

theorem pinv_stepA {iv : Val} {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {x y : Config APrim ALog} (hI : PInvA iv ε c x) (hs : ClightL.step (aprims ε c) x = some y) :
    PInvA iv ε c y := by
  obtain ⟨hx0, S, H, hg, hA⟩ := hI
  rcases Link.step_cases (t := thr x) (a := x.abs) hs with ⟨habs, hall⟩ | ⟨-, hQ⟩
  · have hAy : AtA iv c (S.lk iv.toNat) (thr y) := by
      rcases own_stepA hc hg hA (hall (aprims noEnvA c) (apull ε c x.abs)) with ⟨-, hA'⟩ | ⟨S', H', hr, hA'⟩
      · simpa using hA'
      · simp only [CThread.cfg] at hr; rw [hg] at hr; cases hr; simpa using hA'
    exact ⟨habs ▸ hx0, S, H, by rw [habs]; exact hg, hAy⟩
  · have hs' : ClightL.step (aprims noEnvA c) ((thr x).cfg (apull ε c x.abs)) = some y :=
      hQ _ _ fun p args => aprims_pull (by rw [apull_noEnvA]) p args
    rcases own_stepA hc hg hA hs' with ⟨he, hA'⟩ | ⟨S', H', hr, hA'⟩
    · exact ⟨⟨S, H, he ▸ hg⟩, at_pullA hR (he ▸ hg) hA'⟩
    · exact ⟨⟨S', H', hr⟩, at_pullA hR hr hA'⟩

theorem pinv_starA {iv : Val} {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c) :
    ∀ {a b}, Star (aprims ε c) a b → PInvA iv ε c a → PInvA iv ε c b := by
  intro a b hab
  induction hab with
  | refl => exact id
  | step hs _ ih => exact fun hI => ih (pinv_stepA hc hR hI hs)

/-- **Per-CPU guarantee** of `acquire(lk); release(lk)`, on `L0[c]` alone:
started idle on its lock at any valid log, under any rely-respecting
environment, the CPU only produces valid logs. -/
theorem client_guarA {c : CPU} (hc : c < NCPU) {iv : Val} {σ : Locals} (hk : σ "lk" = iv)
    {l0 : ALog} {S0 : AState} {H0 : HLogA} (hl0 : areplay l0 = some (S0, H0))
    (hidle : (S0.lk iv.toNat).phase c = .idle) : GuarA c ⟨code, .stop, σ⟩ l0 := by
  intro ε hR x hx
  exact (pinv_starA (iv := iv) hc hR hx ⟨⟨S0, H0, hl0⟩, at_pullA hR hl0 (.q0 hk hidle)⟩).1

/-- The critical section: after `hold`, until `inc_n`. -/
def InCSA (t : CThread APrim) : Prop :=
  (t.stmt = .skip ∧ t.cont = .seq (.call "v" .pull [lkE]) KR) ∨
  (t.stmt = .call "v" .pull [lkE] ∧ t.cont = KR) ∨ (t.stmt = .skip ∧ t.cont = KR) ∨
  (t.stmt = releaseA ∧ t.cont = .stop) ∨
  (t.stmt = .call "_" .push [lkE, .var "v"] ∧ t.cont = .seq (.call "_" .incNow [lkE]) .stop) ∨
  (t.stmt = .skip ∧ t.cont = .seq (.call "_" .incNow [lkE]) .stop) ∨
  (t.stmt = .call "_" .incNow [lkE] ∧ t.cont = .stop)

theorem at_csA {iv : Val} {c : CPU} {p : PState} {t : CThread APrim} (hA : AtA iv c p t)
    (hcs : InCSA t) : ∃ tn, p.phase c = .holding tn := by
  cases hA <;> simp_all [InCSA, KR, KLA, code, acquireA, releaseA, restS, gnA, holdPullS, loopA, lgEA]

theorem client_csA {c : CPU} (hc : c < NCPU) {iv : Val} {σ : Locals} (hk : σ "lk" = iv)
    {ε : AEnv} (hR : RelyA ε c) {x : Config APrim ALog}
    (hx : Star (aprims ε c) (CThread.cfg ⟨code, .stop, σ⟩ []) x) (hcs : InCSA (thr x)) :
    ∃ S H tn, areplay x.abs = some (S, H) ∧ (S.lk iv.toNat).phase c = .holding tn := by
  obtain ⟨⟨S, H, hr⟩, S', H', hr', hA⟩ :=
    pinv_starA (iv := iv) hc hR hx ⟨⟨_, _, rfl⟩, at_pullA hR rfl (.q0 hk rfl)⟩
  obtain ⟨tn, htn⟩ := at_csA hA hcs
  have := (others_events _ (ε.noSelf c x.abs) hr hr').1 iv.toNat
  exact ⟨S, H, tn, hr, this ▸ htn⟩

/-! ## The multicore machine -/

/-- `T` CPUs; CPU `c` runs `acquire(L c); release(L c)`. -/
def poolA (T : Nat) (L : Nat → Val) : List (CThread APrim) :=
  (List.range T).map fun c => ⟨code, .stop, fun z => if z = "lk" then L c else 0⟩

theorem poolA_get {T : Nat} {L : Nat → Val} {c : Nat} (hc : c < (poolA T L).length) :
    (poolA T L)[c] = ⟨code, .stop, fun z => if z = "lk" then L c else 0⟩ := by
  simp [poolA]

theorem pool_guarA (T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) :
    ∀ c (hc : c < (poolA T L).length), GuarA c (poolA T L)[c] [] := by
  intro c hc
  have hcT : c < T := by simpa [poolA] using hc
  rw [poolA_get]
  exact client_guarA (iv := L c) (Nat.lt_of_lt_of_le hcT hT) (by simp) rfl rfl

/-- **Multicore linking for the lock array.** Every run is explained by the
per-CPU layers, and the global log is valid. -/
theorem array_linked (T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) {cs : List (CThread APrim)} {l : ALog}
    (h : CSteps PGA (poolA T L) [] cs l) : LinkedA (poolA T L) [] cs l :=
  composeA (pool_guarA T L hT) ⟨_, _, rfl⟩ h

/-- **Per-lock mutual exclusion on the multicore machine, by linking.** Two CPUs
inside their critical sections on the same lock are the same CPU. -/
theorem multicore_cs_exclusiveA (T : Nat) (L : Nat → Val) (hT : T ≤ NCPU)
    {cs : List (CThread APrim)} {l : ALog} (h : CSteps PGA (poolA T L) [] cs l)
    (c d : Nat) (hc : c < cs.length) (hd : d < cs.length) (hlk : (L c).toNat = (L d).toNat)
    (hcc : InCSA cs[c]) (hdc : InCSA cs[d]) : c = d := by
  have hQ := transferA (pool_guarA T L hT) ⟨_, _, rfl⟩
    (Q := fun c x => InCSA (thr x) → ∃ S H tn, areplay x.abs = some (S, H) ∧
      (S.lk (L c).toNat).phase c = .holding tn)
    (fun c hc ε hR x hx hcs => by
      have hcT : c < T := by simpa [poolA] using hc
      rw [poolA_get] at hx
      exact client_csA (iv := L c) (Nat.lt_of_lt_of_le hcT hT) (by simp) hR hx hcs) h
  obtain ⟨⟨Sg, Hg, hl⟩, -⟩ := array_linked T L hT h
  have glob : ∀ c (hc : c < cs.length), InCSA cs[c] → ∃ tn, (Sg.lk (L c).toNat).phase c = .holding tn := by
    intro c hc hcs
    obtain ⟨lc, xs, hQc, rfl, hx⟩ := hQ c hc
    obtain ⟨S, H, tn, hr, hph⟩ := hQc hcs
    exact ⟨tn, (others_events xs hx hr hl).1 _ ▸ hph⟩
  obtain ⟨t, ht⟩ := glob c hc hcc
  obtain ⟨u, hu⟩ := glob d hd hdc
  rw [hlk] at ht
  exact amutex hl _ ⟨t, ht⟩ ⟨u, hu⟩

end ArrayLinkClient
