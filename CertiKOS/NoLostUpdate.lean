import CertiKOS.ArrayLinkClient
import CertiKOS.CountTN

/-!
# No lost updates: `pull`/`push` data on the multicore machine

Each CPU `c` runs
```
acquire(L c);     // ticket loop, hold, v = pull(L c)
v = v + 1;
release(L c);     // push(L c, v); inc_n(L c)
```
on the shared-log multicore machine. CPUs may share locks. The theorem
`no_lost_updates`: when every CPU has finished, block `i` holds exactly the
number of CPUs that used lock `i` (mod 2³²). No increment is lost, however the
CPUs interleave.

* `AtD`: the program points of this client. Each is tied to its lock's
  protocol state and, inside the critical section, to the block's current
  contents `m`: after `pull`, `v = m`; after the increment, `v = m + 1`.
* `own_stepD`, `at_otherD`: a step of the CPU, and another CPU's event,
  preserve it. Another CPU's `push` cannot change a block we are working on:
  pushing needs the lock (ownership), and we hold it (mutual exclusion).
* `GD`: the global invariant. Each CPU is at a point; each CPU's pushes are
  on its own lock and number 0 or 1 according to its point; and every block
  holds the number of pushes made on it.
-/

namespace NoLostUpdate

open ClightL Ticket ClightToPy LockArray LinkA TicketLive ArrayLinkClient TicketCount

/-! ## The client -/

def incV : Stmt APrim := .assign "v" (.bin .add (.var "v") (.const 1))
def code2 : Stmt APrim := .seq acquireA (.seq incV releaseA)
def KR2 : Cont APrim := .seq (.seq incV releaseA) .stop
def KL2 : Cont APrim := .loop lgEA gnA (.seq holdPullS KR2)

/-- CPU `c` on lock `iv` is at a program point consistent with that lock's
protocol state `p`, and with the block's contents `m` in the critical section. -/
inductive AtD (iv : Val) (c : CPU) (p : PState) (m : Val) : CThread APrim → Prop
  | q0 {σ} : σ "lk" = iv → p.phase c = .idle → AtD iv c p m ⟨code2, .stop, σ⟩
  | q1 {σ} : σ "lk" = iv → p.phase c = .idle → AtD iv c p m ⟨acquireA, KR2, σ⟩
  | q2 {σ} : σ "lk" = iv → p.phase c = .idle → AtD iv c p m ⟨.call "t" .faiTicket [lkE], .seq restS KR2, σ⟩
  | q3 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtD iv c p m ⟨.skip, .seq restS KR2, σ⟩
  | q4 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtD iv c p m ⟨restS, KR2, σ⟩
  | q5 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtD iv c p m ⟨gnA, .seq (.seq loopA holdPullS) KR2, σ⟩
  | q6 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn →
      AtD iv c p m ⟨.skip, .seq (.seq loopA holdPullS) KR2, σ⟩
  | q7 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtD iv c p m ⟨.seq loopA holdPullS, KR2, σ⟩
  | q8 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtD iv c p m ⟨loopA, .seq holdPullS KR2, σ⟩
  | q9 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtD iv c p m ⟨gnA, KL2, σ⟩
  | q10 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtD iv c p m ⟨.skip, KL2, σ⟩
  | q11 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtD iv c p m ⟨.skip, .seq holdPullS KR2, σ⟩
  | q12 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtD iv c p m ⟨holdPullS, KR2, σ⟩
  | q13 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn →
      AtD iv c p m ⟨.call "_" .hold [lkE], .seq (.call "v" .pull [lkE]) KR2, σ⟩
  | q14 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtD iv c p m ⟨.skip, .seq (.call "v" .pull [lkE]) KR2, σ⟩
  | q15 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtD iv c p m ⟨.call "v" .pull [lkE], KR2, σ⟩
  | q16 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → σ "v" = m → AtD iv c p m ⟨.skip, KR2, σ⟩
  | r0 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → σ "v" = m →
      AtD iv c p m ⟨.seq incV releaseA, .stop, σ⟩
  | r1 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → σ "v" = m →
      AtD iv c p m ⟨incV, .seq releaseA .stop, σ⟩
  | r2 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → σ "v" = m + 1 →
      AtD iv c p m ⟨.skip, .seq releaseA .stop, σ⟩
  | q17 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → σ "v" = m + 1 → AtD iv c p m ⟨releaseA, .stop, σ⟩
  | q18 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → σ "v" = m + 1 →
      AtD iv c p m ⟨.call "_" .push [lkE, .var "v"], .seq (.call "_" .incNow [lkE]) .stop, σ⟩
  | q19 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtD iv c p m ⟨.skip, .seq (.call "_" .incNow [lkE]) .stop, σ⟩
  | q20 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtD iv c p m ⟨.call "_" .incNow [lkE], .stop, σ⟩
  | done {σ} : σ "lk" = iv → p.phase c = .idle → AtD iv c p m ⟨.skip, .stop, σ⟩

/-- The points whose local `v` is tied to the block's contents. -/
def InData (t : CThread APrim) : Prop :=
  (t.stmt = .skip ∧ t.cont = KR2) ∨ (t.stmt = .seq incV releaseA ∧ t.cont = .stop) ∨
  (t.stmt = incV ∧ t.cont = .seq releaseA .stop) ∨ (t.stmt = .skip ∧ t.cont = .seq releaseA .stop) ∨
  (t.stmt = releaseA ∧ t.cont = .stop) ∨
  (t.stmt = .call "_" .push [lkE, .var "v"] ∧ t.cont = .seq (.call "_" .incNow [lkE]) .stop)

open Classical in
/-- Has this CPU pushed yet? -/
noncomputable def flag (t : CThread APrim) : Nat :=
  if (t.stmt = .skip ∧ t.cont = .seq (.call "_" .incNow [lkE]) .stop) ∨
     (t.stmt = .call "_" .incNow [lkE] ∧ t.cont = .stop) ∨ (t.stmt = .skip ∧ t.cont = .stop) then 1 else 0

local macro "dsimp_defs" : tactic => `(tactic| simp [InData, flag, thr, CThread.cfg, KR2, KL2, code2, incV, acquireA, releaseA,
  restS, gnA, holdPullS, loopA, lgEA, lkE])

theorem atD_mem {iv : Val} {c : CPU} {p : PState} {m m' : Val} {t : CThread APrim}
    (hA : AtD iv c p m t) (hm : InData t → m' = m) : AtD iv c p m' t := by
  cases hA with
  | q0 a b => exact .q0 a b
  | q1 a b => exact .q1 a b
  | q2 a b => exact .q2 a b
  | q3 a b => exact .q3 a b
  | q4 a b => exact .q4 a b
  | q5 a b => exact .q5 a b
  | q6 a b d => exact .q6 a b d
  | q7 a b d => exact .q7 a b d
  | q8 a b d => exact .q8 a b d
  | q9 a b => exact .q9 a b
  | q10 a b d => exact .q10 a b d
  | q11 a b d => exact .q11 a b d
  | q12 a b d => exact .q12 a b d
  | q13 a b d => exact .q13 a b d
  | q14 a b => exact .q14 a b
  | q15 a b => exact .q15 a b
  | q16 a b d => exact .q16 a b (by rw [hm (by dsimp_defs)]; exact d)
  | r0 a b d => exact .r0 a b (by rw [hm (by dsimp_defs)]; exact d)
  | r1 a b d => exact .r1 a b (by rw [hm (by dsimp_defs)]; exact d)
  | r2 a b d => exact .r2 a b (by rw [hm (by dsimp_defs)]; exact d)
  | q17 a b d => exact .q17 a b (by rw [hm (by dsimp_defs)]; exact d)
  | q18 a b d => exact .q18 a b (by rw [hm (by dsimp_defs)]; exact d)
  | q19 a b => exact .q19 a b
  | q20 a b => exact .q20 a b
  | done a b => exact .done a b

theorem atD_data_hold {iv : Val} {c : CPU} {p : PState} {m : Val} {t : CThread APrim}
    (hA : AtD iv c p m t) (hd : InData t) : ∃ tn, p.phase c = .holding tn := by
  cases hA <;> first | exact ⟨_, ‹_ = Phase.holding _›⟩ | (exfalso; revert hd; dsimp_defs)

theorem at_otherD {iv : Val} {c : CPU} {p p' : PState} {m : Val} {e : Event} {o : Option HEvent}
    {t : CThread APrim} (hi : Inv p) (hp : pstep p e = some (p', o)) (hne : e.cpu ≠ c)
    (hA : AtD iv c p m t) : AtD iv c p' m t := by
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
  | q16 hk h d => exact .q16 hk (hH h) d
  | r0 hk h d => exact .r0 hk (hH h) d
  | r1 hk h d => exact .r1 hk (hH h) d
  | r2 hk h d => exact .r2 hk (hH h) d
  | q17 hk h d => exact .q17 hk (hH h) d
  | q18 hk h d => exact .q18 hk (hH h) d
  | q19 hk h => exact .q19 hk (hH h)
  | q20 hk h => exact .q20 hk (hH h)
  | done hk h => exact .done hk (hI h)

theorem at_othersD {iv : Val} {c : CPU} {m : Val} {t : CThread APrim} :
    ∀ (xs : ALog) {l : ALog} {S S' : AState} {H H' : HLogA},
      (∀ e ∈ xs, e.cpu ≠ c) → areplay l = some (S, H) → areplay (xs ++ l) = some (S', H') →
      AtD iv c (S.lk iv.toNat) m t → AtD iv c (S'.lk iv.toNat) m t
  | [], l, S, S', H, H', _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact hA
  | e :: xs, l, S, S', H, H', hx, hl, hr, hA => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := areplay_cons hr
    have hA2 := at_othersD xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA
    rcases astep_lkA hp iv.toNat with h | ⟨k, o', hps⟩
    · rw [h]; exact hA2
    · exact at_otherD (replay_inv (areplay_proj hl2 iv.toNat)) hps (hx e List.mem_cons_self) hA2

/-! ## Our own step -/

def isPush : AKind → Bool
  | .push _ => true
  | _ => false

def pushes (ys : ALog) : Nat := ys.countP fun e => isPush e.kind

/-- What one step of CPU `c` (on lock `iv`) does: it stays at a program point,
and adds at most one event, its own and on its lock. If that event is a
`push`, it adds one to the block, which `c` holds, and `c` is now "pushed". -/
def Out (iv : Val) (c : CPU) (l : ALog) (S : AState) (t : CThread APrim) (c' : Config APrim ALog) : Prop :=
  ∃ S' H', areplay c'.abs = some (S', H') ∧ AtD iv c (S'.lk iv.toNat) (memOf iv.toNat c'.abs) (thr c') ∧
    ∃ ys, c'.abs = ys ++ l ∧ (∀ e ∈ ys, e.cpu = c ∧ e.lk = iv.toNat) ∧
      ((pushes ys = 0 ∧ flag (thr c') = flag t) ∨
       (pushes ys = 1 ∧ flag (thr c') = flag t + 1 ∧ memOf iv.toNat c'.abs = memOf iv.toNat l + 1 ∧
         Holding S c iv.toNat))

theorem out_nonev {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {c' : Config APrim ALog} (hl : areplay l = some (S, H)) (habs : c'.abs = l)
    (hA : AtD iv c (S.lk iv.toNat) (memOf iv.toNat l) (thr c')) (hf : flag (thr c') = flag t) :
    Out iv c l S t c' :=
  ⟨S, H, habs ▸ hl, habs ▸ hA, [], by simp [habs], by simp, .inl ⟨by simp [pushes], hf⟩⟩

theorem out_tk {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {c' : Config APrim ALog} {k : EvKind} {p' : PState} {o : Option HEvent}
    (hl : areplay l = some (S, H)) (hps : pstep (S.lk iv.toNat) ⟨c, k⟩ = some (p', o))
    (habs : c'.abs = ev c iv.toNat k :: l)
    (hA : AtD iv c p' (memOf iv.toNat l) (thr c')) (hf : flag (thr c') = flag t) :
    Out iv c l S t c' := by
  refine ⟨_, _, habs ▸ areplay_cons_of hl (astep_tk hps), ?_, [ev c iv.toNat k], habs, ?_,
    .inl ⟨by simp [pushes, ev, isPush], hf⟩⟩
  · rw [habs]; simpa [memOf, ev] using hA
  · simp [ev]

theorem out_pull {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {c' : Config APrim ALog} (hl : areplay l = some (S, H)) (hh : Holding S c iv.toNat)
    (habs : c'.abs = ⟨c, iv.toNat, .pull⟩ :: l)
    (hA : AtD iv c (S.lk iv.toNat) (memOf iv.toNat l) (thr c')) (hf : flag (thr c') = flag t) :
    Out iv c l S t c' := by
  have hp : astep S ⟨c, iv.toNat, .pull⟩ = some (S, none) := by simp [astep, hh]
  refine ⟨_, _, habs ▸ areplay_cons_of hl hp, ?_, [⟨c, iv.toNat, .pull⟩], habs, by simp,
    .inl ⟨by simp [pushes, isPush], hf⟩⟩
  rw [habs]; simpa [memOf] using hA

theorem own_stepD {iv : Val} {c : CPU} {l : ALog} {S : AState} {H : HLogA} {t : CThread APrim}
    {c' : Config APrim ALog} (hc : c < NCPU) (hl : areplay l = some (S, H))
    (hA : AtD iv c (S.lk iv.toNat) (memOf iv.toNat l) t)
    (hst : ClightL.step (aprims noEnvA c) (t.cfg l) = some c') : Out iv c l S t c' := by
  have hpr := areplay_proj hl iv.toNat
  have hi := replay_inv hpr
  obtain ⟨hn, htk⟩ := replay_counts hpr
  cases hA with
  | q0 hk hp =>
    simp only [ClightL.step, CThread.cfg, code2, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q1 hk hp) (by dsimp_defs)
  | q1 hk hp =>
    simp only [ClightL.step, CThread.cfg, acquireA_eq, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q2 hk hp) (by dsimp_defs)
  | @q2 σ hk hp =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incTicket⟩ = some (⟨(S.lk iv.toNat).ticket + 1,
        (S.lk iv.toNat).now, setPhase (S.lk iv.toNat).phase c (.waiting (S.lk iv.toNat).ticket)⟩, none) := by
      simp [pstep, hc, hp]
    exact out_tk hl hps rfl (.q3 (tn := (S.lk iv.toNat).ticket) (by simp [hk]) ⟨by simp, by simp [htk]⟩)
      (by dsimp_defs)
  | q3 hk hw =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q4 hk hw) (by dsimp_defs)
  | q4 hk hw =>
    simp only [ClightL.step, CThread.cfg, restS, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q5 hk hw) (by dsimp_defs)
  | @q5 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine out_tk hl hps rfl (.q6 (tn := tn) (by simp [hk]) ⟨hw.1, by simp [hw.2]⟩ ?_) (by dsimp_defs)
    rw [← hn]; exact nInv_fresh hi hw.1 σ
  | q6 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q7 hk hw hni) (by dsimp_defs)
  | q7 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q8 hk hw hni) (by dsimp_defs)
  | @q8 σ tn hk hw hni =>
    change ClightL.step _ (CThread.cfg ⟨.while lgEA gnA, .seq holdPullS KR2, σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    by_cases hz : lgEA.eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have heq : σ "n" = σ "t" := by rw [lgEA, ne_eval_zero] at hz; simpa [Expr.eval] using hz
      exact out_nonev hl rfl (.q11 hk hw (nInv_exit hi hw hni heq)) (by dsimp_defs)
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      exact out_nonev hl rfl (.q9 hk hw) (by dsimp_defs)
  | @q9 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine out_tk hl hps rfl (.q10 (tn := tn) (by simp [hk]) ⟨hw.1, by simp [hw.2]⟩ ?_) (by dsimp_defs)
    rw [← hn]; exact nInv_fresh hi hw.1 σ
  | q10 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, KL2, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q8 hk hw hni) (by dsimp_defs)
  | q11 hk hw h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q12 hk hw h) (by dsimp_defs)
  | q12 hk hw h =>
    simp only [ClightL.step, CThread.cfg, holdPullS, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q13 hk hw h) (by dsimp_defs)
  | @q13 σ tn hk hw h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .hold⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now,
        setPhase (S.lk iv.toNat).phase c (.holding tn)⟩, some (.acq c)) := by
      simp [pstep, hc, hw.1, h]
    exact out_tk hl hps rfl (.q14 (tn := tn) (by simp [hk]) (by simp)) (by dsimp_defs)
  | q14 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q15 hk h) (by dsimp_defs)
  | @q15 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    exact out_pull hl ⟨tn, h⟩ rfl (.q16 (tn := tn) (by simp [hk]) h (by simp)) (by dsimp_defs)
  | q16 hk h d =>
    simp only [ClightL.step, CThread.cfg, KR2, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.r0 hk h d) (by dsimp_defs)
  | r0 hk h d =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.r1 hk h d) (by dsimp_defs)
  | @r1 σ tn hk h d =>
    simp only [ClightL.step, CThread.cfg, incV, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.r2 (tn := tn) (by simp [hk]) h (by simp [Expr.eval, BinOp.eval, d]))
      (by dsimp_defs)
  | r2 hk h d =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q17 hk h d) (by dsimp_defs)
  | q17 hk h d =>
    simp only [ClightL.step, CThread.cfg, releaseA_eq, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q18 hk h d) (by dsimp_defs)
  | @q18 σ tn hk h d =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hpu : astep S ⟨c, iv.toNat, .push (σ "v")⟩ =
        some (⟨S.lk, upd S.mem iv.toNat (σ "v"), upd S.dirty iv.toNat true⟩, none) := by
      simp [astep, Holding, h]
    refine ⟨_, _, areplay_cons_of hl hpu, .q19 (tn := tn) (by simp [hk]) h, [⟨c, iv.toNat, .push (σ "v")⟩],
      rfl, by simp, .inr ⟨by simp [pushes, isPush], by dsimp_defs, by simp [memOf, d], ⟨tn, h⟩⟩⟩
  | q19 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact out_nonev hl rfl (.q20 hk h) (by dsimp_defs)
  | @q20 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, aprims, lkE, List.map, Expr.eval, hk, apull_noEnvA,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incNow⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now + 1,
        setPhase (S.lk iv.toNat).phase c .idle⟩, some (.rel c)) := by
      simp [pstep, hc, h]
    exact out_tk hl hps rfl (.done (by simp [hk]) (by simp)) (by dsimp_defs)
  | done hk h => simp [ClightL.step, CThread.cfg] at hst

/-! ## Counting pushes -/

def pushBy (c j : Nat) (l : ALog) : Nat :=
  l.countP fun e => decide (e.cpu = c) && decide (e.lk = j) && isPush e.kind

def pushOn (j : Nat) (l : ALog) : Nat := l.countP fun e => decide (e.lk = j) && isPush e.kind

theorem memOf_append_other {j : Nat} : ∀ {ys : ALog}, (∀ e ∈ ys, e.lk ≠ j) → ∀ l, memOf j (ys ++ l) = memOf j l
  | [], _, l => rfl
  | ⟨d, k, a⟩ :: ys, h, l => by
    have hk : k ≠ j := h _ List.mem_cons_self
    have ih := memOf_append_other (ys := ys) (fun e he => h e (List.mem_cons_of_mem _ he)) l
    cases a <;> simp [memOf, hk, ih]

theorem memOf_append_nopush {j : Nat} : ∀ {ys : ALog}, pushes ys = 0 → ∀ l, memOf j (ys ++ l) = memOf j l
  | [], _, l => rfl
  | ⟨d, k, a⟩ :: ys, h, l => by
    cases a with
    | push v => simp [pushes, isPush] at h
    | tk kk =>
      have : pushes ys = 0 := by simpa [pushes, isPush] using h
      simp [memOf, memOf_append_nopush this l]
    | pull =>
      have : pushes ys = 0 := by simpa [pushes, isPush] using h
      simp [memOf, memOf_append_nopush this l]

theorem pushBy_own {a i : Nat} : ∀ {ys : ALog}, (∀ e ∈ ys, e.cpu = a ∧ e.lk = i) →
    ∀ c j, pushBy c j ys = if c = a ∧ j = i then pushes ys else 0
  | [], _, c, j => by simp [pushBy, pushes]
  | e :: ys, h, c, j => by
    have ih := pushBy_own (ys := ys) (fun e he => h e (List.mem_cons_of_mem _ he)) c j
    obtain ⟨h1, h2⟩ := h e List.mem_cons_self
    simp only [pushBy, pushes, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases hc : c = a <;> by_cases hj : j = i <;> simp [hc, hj, h1, h2] <;> omega

theorem pushOn_own {a i : Nat} : ∀ {ys : ALog}, (∀ e ∈ ys, e.cpu = a ∧ e.lk = i) →
    ∀ j, pushOn j ys = if j = i then pushes ys else 0
  | [], _, j => by simp [pushOn, pushes]
  | e :: ys, h, j => by
    have ih := pushOn_own (ys := ys) (fun e he => h e (List.mem_cons_of_mem _ he)) j
    obtain ⟨-, h2⟩ := h e List.mem_cons_self
    simp only [pushOn, pushes, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases hj : j = i <;> simp [hj, h2] <;> omega

theorem sumTo_ind' (a : Nat) (P : Prop) [Decidable P] : ∀ n,
    sumTo (fun c => if a = c ∧ P then 1 else 0) n = if a < n ∧ P then 1 else 0
  | 0 => by simp [sumTo]
  | n + 1 => by
    simp only [sumTo, sumTo_ind' a P n]
    by_cases hP : P
    · simp only [hP, and_true]
      by_cases h1 : a < n
      · have h2 : a ≠ n := Nat.ne_of_lt h1
        simp [h1, h2, Nat.lt_succ_of_lt h1]
      · by_cases h2 : a = n
        · simp [h2]
        · have h3 : ¬ a < n + 1 := fun h =>
            h2 (Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_not_lt h1))
          simp [h1, h2, h3]
    · simp [hP]

theorem pushOn_split (j T : Nat) : ∀ l : ALog, (∀ e ∈ l, e.cpu < T) →
    pushOn j l = sumTo (fun c => pushBy c j l) T
  | [], _ => by
    rw [sumTo_congr (g := fun _ => 0) T (fun c _ => by simp [pushBy]), sumTo_const]; simp [pushOn]
  | e :: l, h => by
    have ih := pushOn_split j T l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    have hs : (fun c => pushBy c j (e :: l)) =
        fun c => pushBy c j l + (if e.cpu = c ∧ (e.lk = j ∧ isPush e.kind = true) then 1 else 0) := by
      funext c; simp only [pushBy, List.countP_cons]
      by_cases h1 : e.cpu = c <;> by_cases h2 : e.lk = j <;> cases isPush e.kind <;> simp [h1, h2]
    rw [hs, sumTo_add, sumTo_ind', ← ih]
    simp only [pushOn, List.countP_cons]
    by_cases h2 : e.lk = j <;> cases isPush e.kind <;> simp [h2, he]

/-! ## The global invariant -/

/-- `T` CPUs; CPU `c` runs `acquire(L c); v = v + 1; release(L c)`. -/
def poolD (T : Nat) (L : Nat → Val) : List (CThread APrim) :=
  (List.range T).map fun c => ⟨code2, .stop, fun z => if z = "lk" then L c else 0⟩

def GD (T : Nat) (L : Nat → Val) (cs : List (CThread APrim)) (l : ALog) : Prop :=
  ∃ S H, areplay l = some (S, H) ∧ cs.length = T ∧ (∀ e ∈ l, e.cpu < T) ∧
    (∀ c (hc : c < cs.length), AtD (L c) c (S.lk (L c).toNat) (memOf (L c).toNat l) cs[c]) ∧
    (∀ c (hc : c < cs.length), ∀ j, pushBy c j l = if j = (L c).toNat then flag cs[c] else 0) ∧
    (∀ j, memOf j l = BitVec.ofNat 32 (pushOn j l))

theorem gd_init (T : Nat) (L : Nat → Val) : GD T L (poolD T L) [] := by
  refine ⟨_, _, rfl, by simp [poolD], by simp, fun c hc => ?_, fun c hc j => ?_, fun j => rfl⟩
  · simp only [poolD, List.getElem_map, List.getElem_range]
    exact .q0 (by simp) rfl
  · simp only [poolD, List.getElem_map, List.getElem_range]
    simp [pushBy, flag, code2, acquireA]

theorem gd_step {T : Nat} {L : Nat → Val} (hT : T ≤ NCPU) {cs cs' : List (CThread APrim)} {l l' : ALog}
    (hG : GD T L cs l) (hS : CStep PGA cs l cs' l') : GD T L cs' l' := by
  obtain ⟨S, H, hl, hlen, hev, hAt, hpb, hmem⟩ := hG
  cases hS with
  | step a ha hst =>
  have haT : a < T := hlen ▸ ha
  have haN : a < NCPU := Nat.lt_of_lt_of_le haT hT
  obtain ⟨S', H', hr', hA', ys, hys, hown, hcase⟩ := own_stepD haN hl (hAt a ha) hst
  have hr'' : areplay (ys ++ l) = some (S', H') := hys ▸ hr'
  refine ⟨S', H', hr', by simpa using hlen, fun e he => ?_, fun c hc => ?_, fun c hc j => ?_, fun j => ?_⟩
  · rw [hys] at he
    rcases List.mem_append.1 he with he | he
    · rw [(hown e he).1]; exact haT
    · exact hev e he
  · by_cases hca : c = a
    · subst hca; simpa only [List.getElem_set_self] using hA'
    · have hc' : c < cs.length := by simpa using hc
      simp only [List.getElem_set_ne (Ne.symm hca)]
      have hx : ∀ e ∈ ys, e.cpu ≠ c := fun e he => by rw [(hown e he).1]; exact Ne.symm hca
      have hA1 := at_othersD ys hx hl hr'' (hAt c hc')
      rw [hys]
      refine atD_mem hA1 fun hd => ?_
      by_cases hli : (L c).toNat = (L a).toNat
      · rcases hcase with ⟨h0, -⟩ | ⟨-, -, -, hhold⟩
        · exact memOf_append_nopush h0 l
        · exfalso
          obtain ⟨tn, htn⟩ := atD_data_hold (hAt c hc') hd
          rw [hli] at htn
          exact hca (amutex hl _ ⟨tn, htn⟩ hhold)
      · exact memOf_append_other (fun e he => by rw [(hown e he).2]; exact Ne.symm hli) l
  · have hc' : c < cs.length := by simpa using hc
    rw [hys, pushBy, List.countP_append, ← pushBy, ← pushBy, pushBy_own hown, hpb c hc' j]
    by_cases hca : c = a
    · subst hca
      simp only [List.getElem_set_self]
      by_cases hj : j = (L c).toNat
      · rcases hcase with ⟨h0, hf⟩ | ⟨h1, hf, -, -⟩
        · simp [hj, hf, h0]
        · simp [hj, hf, h1]; omega
      · simp [hj]
    · simp only [List.getElem_set_ne (Ne.symm hca)]; simp [hca]
  · rw [hys, pushOn, List.countP_append, ← pushOn, ← pushOn, pushOn_own hown]
    by_cases hj : j = (L a).toNat
    · subst hj
      rcases hcase with ⟨h0, -⟩ | ⟨h1, -, hm, -⟩
      · rw [memOf_append_nopush h0 l, hmem]; simp [h0]
      · rw [← hys, hm, hmem]; simp only [h1, if_pos rfl]
        rw [Nat.add_comm]; exact ofNat_succ _
    · rw [memOf_append_other (fun e he => by rw [(hown e he).2]; exact Ne.symm hj) l, hmem]; simp [hj]

theorem gd_steps {T : Nat} {L : Nat → Val} (hT : T ≤ NCPU) {cs : List (CThread APrim)} {l : ALog}
    (h : CSteps PGA (poolD T L) [] cs l) : GD T L cs l := by
  suffices ∀ {a b la lb}, CSteps PGA a la b lb → GD T L a la → GD T L b lb from this h (gd_init T L)
  intro a b la lb hab
  induction hab with
  | refl => exact id
  | step h₁ _ ih => exact fun hG => ih (gd_step hT hG h₁)

/-- **No lost updates.** On the multicore machine, when every CPU has
finished `acquire(L c); v = v + 1; release(L c)`, block `j` holds the number
of CPUs that used lock `j`, mod 2³². However the CPUs interleaved, no
increment was lost. -/
theorem no_lost_updates (T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) {cs : List (CThread APrim)} {l : ALog}
    (h : CSteps PGA (poolD T L) [] cs l)
    (hdone : ∀ c (hc : c < cs.length), cs[c].stmt = .skip ∧ cs[c].cont = .stop) (j : Nat) :
    memOf j l = BitVec.ofNat 32 (sumTo (fun c => if j = (L c).toNat then 1 else 0) T) := by
  obtain ⟨S, H, hl, hlen, hev, -, hpb, hmem⟩ := gd_steps hT h
  rw [hmem, pushOn_split j T l hev]
  congr 1
  refine sumTo_congr T fun c hc => ?_
  have hc' : c < cs.length := by rw [hlen]; exact hc
  rw [hpb c hc' j]
  have hf : flag cs[c] = 1 := by
    obtain ⟨h1, h2⟩ := hdone c hc'
    simp [flag, h1, h2]
  rw [hf]

end NoLostUpdate
