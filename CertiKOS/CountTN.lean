import CertiKOS.LiveLink
import CertiKOS.TicketLive

/-!
# The final count: every thread takes exactly `N` tickets

`TicketLive.python_final` shows `lk.ticket == lk.now` once every Python thread
has finished. Here the value is pinned down: both equal `T * N mod 2³²`.

* `left N t`: the number of acquire/release rounds CPU thread `t` still has
  to *start*. It is read off the program point and the loop counter `i`.
  It is `N` before the loop, `N - i` at the loop head and up to `FAI_t`,
  `N - i - 1` after `FAI_t`, and `0` when done.
* `own_left`: one step of a CPU leaves (own `incTicket` events + `left`)
  unchanged. Only `FAI_t` changes `left`, by exactly one.
* `count_inv`: in every reachable multicore state, each CPU `i < T` has
  `cntC i incTicket l + left N cs[i] = N`, and every event is by a CPU `< T`.
* `final_ticket`: when all CPUs are done, `ticket l = now l = T * N`.
* `python_count`: when all Python threads are done, `lk.ticket` and `lk.now`
  both hold `T * N mod 2³²`.
-/

namespace TicketCount

open ClightL Ticket ClightToPy TicketPy TicketLive Link LiveLink

open Classical in
/-- Rounds still to start, read off the program point and `i`. -/
noncomputable def left (N : Nat) (t : CThread Prim) : Nat :=
  let i := (t.locals "i").toNat
  if t.cont = .stop ∧ t.stmt = .skip then 0
  else if t.cont = .stop ∧ t.stmt = clientCode N then N
  else if t.cont = .seq (loopS N) .stop then N
  else if t.cont = .stop then N - i
  else if t.cont = KO N ∧ t.stmt = bodyS then N - i
  else if t.cont = KO N ∧ t.stmt = .skip then N - i
  else if t.cont = KA N ∧ t.stmt = acquireCode then N - i
  else if t.cont = KT N ∧ t.stmt = .call "t" .faiTicket [] then N - i
  else N - i - 1

theorem toNat_i {σ : Locals} {m N : Nat} (hm : m ≤ N) (hN : N < 2 ^ 32)
    (h : σ "i" = BitVec.ofNat 32 m) : (σ "i").toNat = m := by
  rw [h, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

section Eval
variable (N : Nat) (σ : Locals)
local macro "lsimp" : tactic => `(tactic| simp [left, clientCode, loopS, bodyS, KO, KA, KT, KW, KH, KL,
  KR, acquireCode, acquireLoop, holdCall, releaseCode, incI, gnC, gI, lgE])

theorem l_p0 : left N ⟨clientCode N, .stop, σ⟩ = N := by lsimp
theorem l_p1 : left N ⟨.assign "i" (.const 0), .seq (loopS N) .stop, σ⟩ = N := by lsimp
theorem l_p2 : left N ⟨.skip, .seq (loopS N) .stop, σ⟩ = N := by lsimp
theorem l_p3 : left N ⟨loopS N, .stop, σ⟩ = N - (σ "i").toNat := by lsimp
theorem l_p4 : left N ⟨bodyS, KO N, σ⟩ = N - (σ "i").toNat := by lsimp
theorem l_p5 : left N ⟨acquireCode, KA N, σ⟩ = N - (σ "i").toNat := by lsimp
theorem l_p6 : left N ⟨.call "t" .faiTicket [], KT N, σ⟩ = N - (σ "i").toNat := by lsimp
theorem l_p7 : left N ⟨.skip, KT N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p8 : left N ⟨.seq gnC (.seq acquireLoop holdCall), KA N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p9 : left N ⟨gnC, KW N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p10 : left N ⟨.skip, KW N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p11 : left N ⟨.seq acquireLoop holdCall, KA N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p12 : left N ⟨acquireLoop, KH N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p13 : left N ⟨gnC, KL N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p14 : left N ⟨.skip, KL N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p15 : left N ⟨.skip, KH N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p16 : left N ⟨holdCall, KA N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p17 : left N ⟨.skip, KA N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p18 : left N ⟨.seq releaseCode incI, KO N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p19 : left N ⟨releaseCode, KR N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p20 : left N ⟨.skip, KR N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p21 : left N ⟨incI, KO N, σ⟩ = N - (σ "i").toNat - 1 := by lsimp
theorem l_p22 : left N ⟨.skip, KO N, σ⟩ = N - (σ "i").toNat := by lsimp
theorem l_done : left N ⟨.skip, .stop, σ⟩ = 0 := by lsimp
end Eval

local macro "lsimp" : tactic => `(tactic| simp [thr, left, clientCode, loopS, bodyS, KO, KA, KT, KW, KH,
  KL, KR, acquireCode, acquireLoop, holdCall, releaseCode, incI, gnC, gI, lgE])

/-- **One step of a CPU**: own tickets taken plus rounds left to start is unchanged. -/
theorem own_left {N : Nat} {c : CPU} {s : PState} {l : Log} {t : CThread Prim}
    {w : Nat} {c' : Config Prim Log} (hN : N < 2 ^ 32)
    (hA : At N c s t w) (hst : ClightL.step (prims noEnv c) (t.cfg l) = some c') :
    cntC c .incTicket c'.abs + left N (thr c') = cntC c .incTicket l + left N t := by
  cases hA with
  | p0 hp =>
    simp only [ClightL.step, CThread.cfg, clientCode, Option.some.injEq] at hst; subst hst; lsimp
  | p1 hp =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst; lsimp
  | @p2 σ hp hi0 =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst; lsimp; simp [hi0]
  | @p3 σ m hp hm hiv =>
    change ClightL.step _ (CThread.cfg ⟨.while (gI N) bodyS, .stop, σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    have hti := toNat_i hm hN hiv
    by_cases hz : (gI N).eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have hmN : m = N := by
        rw [gI, ne_eval_zero] at hz; simp only [ClightL.Expr.eval] at hz; rw [hiv] at hz
        exact ofNat_eq_of_close hm (by omega) hz
      simp only [CThread.cfg, thr, l_done]
      rw [l_p3, hti]; omega
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      simp only [CThread.cfg, thr]
      rw [show Cont.loop (gI N) bodyS .stop = KO N from rfl, l_p3, l_p4]
  | p4 hp hit =>
    simp only [ClightL.step, CThread.cfg, bodyS, Option.some.injEq] at hst; subst hst; lsimp
  | p5 hp hit =>
    simp only [ClightL.step, CThread.cfg, acquireCode, Option.some.injEq] at hst; subst hst; lsimp
  | @p6 σ m hp hit =>
    simp only [ClightL.step, CThread.cfg, prims, List.map_nil, pull_noEnv, Option.some.injEq] at hst
    subst hst
    have hti := toNat_i (Nat.le_of_lt hit.1) hN hit.2
    simp only [thr, l_p6, l_p7, cntC_cons_self, Locals.set_other _ _ (by decide : ("i" : String) ≠ "t"), hti]
    have := hit.1; omega
  | p7 hw hit =>
    simp only [ClightL.step, CThread.cfg, KT, Option.some.injEq] at hst; subst hst; lsimp
  | p8 hw hit =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst; lsimp
  | @p9 σ m tn hw hit =>
    simp only [ClightL.step, CThread.cfg, gnC, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    simp only [thr, cntC_cons_other _ (by decide : EvKind.getNow ≠ .incTicket)]
    rw [l_p10, l_p9, Locals.set_other _ _ (by decide : ("i" : String) ≠ "n")]
  | p10 hw hit hni =>
    simp only [ClightL.step, CThread.cfg, KW, Option.some.injEq] at hst; subst hst; lsimp
  | p11 hw hit hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst; lsimp
  | @p12 σ m tn hw hit hni =>
    change ClightL.step _ (CThread.cfg ⟨.while lgE gnC, KH N, σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    by_cases hz : lgE.eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      simp only [CThread.cfg, thr, l_p15]
      rw [l_p12]
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      simp only [CThread.cfg, thr]
      rw [show Cont.loop lgE gnC (KH N) = KL N from rfl, l_p13, l_p12]
  | @p13 σ m tn hw hit =>
    simp only [ClightL.step, CThread.cfg, gnC, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    simp only [thr, cntC_cons_other _ (by decide : EvKind.getNow ≠ .incTicket)]
    rw [l_p14, l_p13, Locals.set_other _ _ (by decide : ("i" : String) ≠ "n")]
  | p14 hw hit hni =>
    simp only [ClightL.step, CThread.cfg, KL, Option.some.injEq] at hst; subst hst; lsimp
  | p15 hw hit hnow =>
    simp only [ClightL.step, CThread.cfg, KH, Option.some.injEq] at hst; subst hst; lsimp
  | @p16 σ m tn hw hit hnow =>
    simp only [ClightL.step, CThread.cfg, holdCall, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    simp only [thr, cntC_cons_other _ (by decide : EvKind.hold ≠ .incTicket)]
    rw [l_p17, l_p16, Locals.set_other _ _ (by decide : ("i" : String) ≠ "_")]
  | p17 hh hit =>
    simp only [ClightL.step, CThread.cfg, KA, Option.some.injEq] at hst; subst hst; lsimp
  | p18 hh hit =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst; lsimp
  | @p19 σ m tn hh hit =>
    simp only [ClightL.step, CThread.cfg, releaseCode, prims, List.map_nil, pull_noEnv,
      Option.some.injEq] at hst
    subst hst
    simp only [thr, cntC_cons_other _ (by decide : EvKind.incNow ≠ .incTicket)]
    rw [l_p20, l_p19, Locals.set_other _ _ (by decide : ("i" : String) ≠ "_")]
  | p20 hp hit =>
    simp only [ClightL.step, CThread.cfg, KR, Option.some.injEq] at hst; subst hst; lsimp
  | @p21 σ m hp hit =>
    simp only [ClightL.step, CThread.cfg, incI, Option.some.injEq] at hst; subst hst
    have hti := toNat_i (Nat.le_of_lt hit.1) hN hit.2
    have hi1 : (σ.set "i" (ClightL.Expr.eval σ (.bin .add (.var "i") (.const 1)))) "i" =
        BitVec.ofNat 32 (m + 1) := by
      simp only [Locals.set_same, ClightL.Expr.eval, ClightL.BinOp.eval, hit.2]; exact ofNat_succ m
    have hti' := toNat_i hit.1 hN hi1
    simp only [thr, l_p22]
    rw [l_p21, hti', hti]; have := hit.1; omega
  | @p22 σ m hp hm hi1 =>
    simp only [ClightL.step, CThread.cfg, KO, Option.some.injEq] at hst; subst hst; lsimp
  | done hp => simp [ClightL.step, CThread.cfg] at hst

/-! ## Summing over CPUs -/

theorem cntC_cons (i : CPU) (k : EvKind) (e : Event) (l : Log) :
    cntC i k (e :: l) = cntC i k l + (if e.cpu = i ∧ e.kind = k then 1 else 0) := by
  simp [cntC, List.countP_cons]

theorem sumTo_add (f g : Nat → Nat) : ∀ n, sumTo (fun i => f i + g i) n = sumTo f n + sumTo g n
  | 0 => rfl
  | n + 1 => by simp only [sumTo, sumTo_add f g n]; omega

theorem sumTo_ind (e : Event) (k : EvKind) : ∀ n,
    sumTo (fun i => if e.cpu = i ∧ e.kind = k then 1 else 0) n = if e.cpu < n ∧ e.kind = k then 1 else 0
  | 0 => by simp [sumTo]
  | n + 1 => by
    simp only [sumTo, sumTo_ind e k n]
    by_cases hk : e.kind = k
    · simp only [hk, and_true]
      by_cases h1 : e.cpu < n
      · have h2 : e.cpu ≠ n := Nat.ne_of_lt h1
        simp [h1, h2, Nat.lt_succ_of_lt h1]
      · by_cases h2 : e.cpu = n
        · simp [h2]
        · have h3 : ¬ e.cpu < n + 1 := fun h =>
            h2 (Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_not_lt h1))
          simp [h1, h2, h3]
    · simp [hk]

theorem sumTo_congr {f g : Nat → Nat} (n : Nat) (h : ∀ i, i < n → f i = g i) : sumTo f n = sumTo g n :=
  Nat.le_antisymm (sumTo_le n fun i hi => Nat.le_of_eq (h i hi)) (sumTo_le n fun i hi => Nat.le_of_eq (h i hi).symm)

/-- Every event is one CPU's: a kind's count is the sum of the CPUs' counts. -/
theorem countK_split (k : EvKind) (T : Nat) : ∀ l : Log, (∀ e ∈ l, e.cpu < T) →
    countK k l = sumTo (fun i => cntC i k l) T
  | [], _ => by
    rw [sumTo_congr (g := fun _ => 0) T (fun i _ => by simp [cntC]), sumTo_const]; simp [countK]
  | e :: l, h => by
    simp only [countK, cntC_cons]
    rw [sumTo_add, sumTo_ind, ← countK_split k T l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    have := h e List.mem_cons_self
    by_cases hk : e.kind = k <;> simp [hk, this] <;> omega

/-! ## The counting invariant on the multicore machine -/

/-- Every event is by a CPU `< T`, and each CPU's tickets taken plus rounds
left to start is `N`. -/
def CI (N T : Nat) (cs : List (CThread Prim)) (l : Log) : Prop :=
  (∀ e ∈ l, e.cpu < T) ∧ ∀ i (hi : i < cs.length), cntC i .incTicket l + left N cs[i] = N

theorem ci_init (T N : Nat) : CI N T (cPool T N) [] :=
  ⟨by simp, fun i hi => by simp only [cPool, List.getElem_replicate, cThread]; rw [l_p0]; simp [cntC]⟩

theorem ci_step {N T : Nat} {cs cs' : List (CThread Prim)} {l l' : Log} {Φ : Nat}
    (hG : GI N T cs l Φ) (hC : CI N T cs l) (hS : CStep PG cs l cs' l') : CI N T cs' l' := by
  obtain ⟨s, h, ws, hl, hlen, -, hN, -, hAt, -⟩ := hG
  obtain ⟨hev, hcnt⟩ := hC
  cases hS with
  | step j hj hst =>
  obtain ⟨ys, hys, hy⟩ := gstep_log hst
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · rw [hys] at he
    rcases List.mem_append.1 he with he | he
    · rw [hy e he, ← hlen]; exact hj
    · exact hev e he
  · by_cases hij : i = j
    · subst hij
      simp only [List.getElem_set_self]
      rw [own_left hN (hAt i hj) hst]; exact hcnt i hj
    · simp only [List.getElem_set_ne (Ne.symm hij)]
      have hi' : i < cs.length := by simpa using hi
      rw [hys, cntC_append, cntC_others (fun e he => by rw [hy e he]; exact Ne.symm hij)]
      simpa using hcnt i hi'

theorem ci_steps {N T : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) {cs : List (CThread Prim)} {l : Log}
    (h : CSteps PG (cPool T N) [] cs l) : CI N T cs l := by
  suffices ∀ {a b la lb}, CSteps PG a la b lb → ∀ {Φ}, GI N T a la Φ → CI N T a la → CI N T b lb from
    this h (ginit T N hT hN) (ci_init T N)
  intro a b la lb hab
  induction hab with
  | refl => exact fun _ h => h
  | step h₁ _ ih =>
    intro Φ hG hC
    obtain ⟨Φ', hG'⟩ := gsteps (.step h₁ .refl) hG
    exact ih hG' (ci_step hG hC h₁)

/-- **The final count on the multicore machine.** When every CPU has finished,
`T * N` tickets were taken and `T * N` served. -/
theorem final_ticket {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) {cs : List (CThread Prim)}
    {l : Log} (h : CSteps PG (cPool T N) [] cs l)
    (hdone : ∀ i (hi : i < cs.length), cs[i].stmt = .skip ∧ cs[i].cont = .stop) :
    ticket l = T * N ∧ now l = T * N := by
  obtain ⟨hev, hcnt⟩ := ci_steps hT hN h
  obtain ⟨Φ, s, hs, ws, hl, hlen, -, -, hidle, hAt, -⟩ := gsteps h (ginit T N hT hN)
  have hall : ∀ i, i < T → cntC i .incTicket l = N := by
    intro i hi
    have hi' : i < cs.length := by rw [hlen]; exact hi
    have := hcnt i hi'
    obtain ⟨h1, h2⟩ := hdone i hi'
    have e : cs[i] = ⟨.skip, .stop, cs[i].locals⟩ := by
      cases hc : cs[i]; simp_all
    rw [e, l_done] at this; omega
  have htk : ticket l = T * N := by
    unfold ticket
    rw [countK_split _ T l hev, sumTo_congr (g := fun _ => N) T hall, sumTo_const]
  refine ⟨htk, ?_⟩
  have hphase : ∀ d, s.phase d = .idle := by
    intro d
    by_cases hd : d < cs.length
    · exact at_done (hAt d hd) ⟨(hdone d hd).1, (hdone d hd).2⟩
    · exact hidle d (by rw [← hlen]; exact Nat.le_of_not_lt hd)
  have hact : active s = 0 := cnt_zero (fun d => by rw [hphase d]; rfl) NCPU
  have hcount := (replay_inv hl).count
  obtain ⟨hn, ht⟩ := replay_counts hl
  omega

/-- **The final count, in Python.** When every thread of the translated client
has finished, `lk.ticket` and `lk.now` both hold `T * N mod 2³²`. -/
theorem python_count {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) {k : Nat} {ts : PyL.Pool}
    {H : PyL.Heap} (h : PyL.MSteps k (pyPool T N) H0 ts H)
    (hdone : ∀ i (hi : i < ts.length), ts[i].cmd = .skip) :
    H tkLoc = some (((T * N : Nat) : Int) % M) ∧ H nwLoc = some (((T * N : Nat) : Int) % M) := by
  obtain ⟨cs, l, hc, hfin, htk, hnw⟩ := python_done T N h hdone
  obtain ⟨h1, h2⟩ := final_ticket hT hN hc hfin
  rw [htk, hnw, h1, h2]; exact ⟨rfl, rfl⟩

end TicketCount
