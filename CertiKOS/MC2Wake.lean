import CertiKOS.MC2Seq
import CertiKOS.MC2Sched

/-!
# mC2: the code of `wakeup`

`wakeup(i)` ([PLDI18] §5.1): take the head of sleeping queue `i`; if it
belongs to this CPU, it goes to the ready queue; otherwise to its CPU's
pending queue. `MC2Sched` has it as two abstract steps, `wake1 i` (the
`deQ`, and the ready queue if the thread is ours) and `wake2` (the `enQ` on
the owner's pending queue). This file writes the code and proves it does
exactly that, on the locks of `MC2Queue`.

**Layout (ours).** Sleeping queue `i` is on lock `sb + i`, and the pending
queue of CPU `d` on lock `pb + d`. Thread `t` belongs to CPU `t % NCPU`
(`ownE`). The ready queue is per-CPU memory, which this machine does not yet
have: the code leaves the thread for the ready queue in the local `rd` (`np`
for none), and the per-CPU layer pushes it.

```
lk = sleep lock i; acquire; r = dequeue(); release;
rd = np;
if (r != np)
  if (r % NCPU == c) rd = r;
  else { pi = r; lk = pend lock (r % NCPU); acquire; enqueue(pi); release; }
```

* `Rdy`: CPU `c` is idle on every lock of a set, and each of those queues is
  a reachable state. `wakeup` starts and ends in it (`rdy_frame` carries it
  across a locked call on one of the locks).
* `wake_code`: **the run of `wakeup(i)`**. The first call finds the replay of
  some history `h1` of sleeping queue `i` and is the event `(c, deQ)`; `t` is
  the head it returns (`taken`). If the queue was empty or `t` is ours, that
  is all, and `rd` is `t` (or `np`). Otherwise the second call finds the
  replay of some history `h2` of the pending queue of `t`'s CPU and is the
  event `(c, enQ t)`, after the first in the log. This is `wake1 i`
  followed, in the second case, by `wake2`.
* `taken_qres`: on the history of a queue in `MC2Sched`'s log, the thread
  the code dequeues is `qres`, the one `wake1` uses. With `own t = t % NCPU`,
  `wake1` puts it on the ready queue exactly when the code leaves it in `rd`.
-/

set_option linter.unusedVariables false

namespace MC2Wake

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region hmemR)
open LockRegionCPU KernFrame Layer LogInv
open MC2 MC2Queue

local notation "v" n => (BitVec.ofNat 32 n : Val)

/-! ## The queues' states -/

theorem replay_lt {np : Nat} : ∀ (h : List (CPU × (Q np).Op)) {q : List Nat},
    (Q np).replay h = some q → ∀ x ∈ q, x < np
  | [], q, hq, x, hx => by
    have e : (Q np).replay [] = some [] := rfl
    rw [e] at hq; have hq' := Option.some.inj hq; subst hq'; simp at hx
  | (c, o) :: h, q, hq, x, hx => by
    have e : (Q np).replay ((c, o) :: h) = (qstep np o ((Q np).replay h)).1 := rfl
    rw [e] at hq
    cases hr : (Q np).replay h with
    | none => rw [hr] at hq; cases o <;> simp [qstep] at hq
    | some q0 =>
      rw [hr] at hq
      have ih := replay_lt h hr
      cases o with
      | enQ t =>
        simp only [qstep] at hq
        split at hq
        · rename_i hc
          have hq' := Option.some.inj hq; subst hq'
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hc.1
          · exact ih x hx
        · simp at hq
      | deQ =>
        simp only [qstep] at hq; have hq' := Option.some.inj hq; subst hq'
        exact ih x (List.dropLast_subset _ hx)

theorem getLastD_mem' {l : List Nat} {d : Nat} (hne : l ≠ []) : l.getLastD d ∈ l := by
  rcases List.eq_nil_or_concat l with h | ⟨l', a, rfl⟩
  · exact absurd h hne
  · rw [List.concat_eq_append, PAbQueue.getLastD_append]; simp

theorem taken_result {np : Nat} {c : CPU} {h : List (CPU × (Q np).Op)} {q : List Nat}
    (hq : (Q np).replay h = some q) : (Q np).result h c .deQ = some (taken np c h) := by
  have e : (Q np).result h c .deQ = some (q.getLastD np) := by
    show (qstep np .deQ ((Q np).replay h)).2 = _; rw [hq]; rfl
  simp [taken, e]

theorem taken_le {np : Nat} {c : CPU} {h : List (CPU × (Q np).Op)} {q : List Nat}
    (hq : (Q np).replay h = some q) : taken np c h ≤ np := by
  have e : (Q np).result h c .deQ = some (q.getLastD np) := by
    show (qstep np .deQ ((Q np).replay h)).2 = _; rw [hq]; rfl
  unfold taken; rw [e]; simp only [Option.getD_some]
  by_cases hne : q = []
  · subst hne; simp [List.getLastD]
  · exact Nat.le_of_lt (replay_lt h hq _ (getLastD_mem' hne))

/-! ## Idle on a set of locks -/

/-- CPU `c` is idle on every lock in `ls`, and each of those queues is a
reachable state. -/
def Rdy (np : Nat) (c : CPU) (ls : Nat → Prop) (S : RState) (H : HLogR) : Prop :=
  ∀ j, ls j → (S.lk j).phase c = .idle ∧ (Q np).J (hmemR j H)

/-- **A locked call on lock `iv` keeps `Rdy`**: the other locks by the
frame, `iv` by the call. -/
theorem rdy_frame {εR : REnv} {c : CPU} {np : Nat} {ls : Nat → Prop}
    (hRJ : ∀ j, ls j → RelyJ εR c j (Q np).J) {s : Stmt APrim} {σ σ' : Locals} {l rb : RLog}
    {S S' : RState} {H H' : HLogR} {iv : Val}
    (hrun : Star (rprimsA εR c) ⟨.seq acquireA (.seq s relA), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩)
    (hown : Own1 s) (hσ : σ "lk" = iv) (hl : rreplay l = some (S, H)) (hrb : rreplay rb = some (S', H'))
    (hR : Rdy np c ls S H) (hid : (S'.lk iv.toNat).phase c = .idle) (hJ : (Q np).J (hmemR iv.toNat H')) :
    Rdy np c ls S' H' := by
  intro j hj
  by_cases e : j = iv.toNat
  · subst e; exact ⟨hid, hJ⟩
  · obtain ⟨hidj, hJj⟩ := hR j hj
    obtain ⟨S4, H4, hl4, hid4, hJ4⟩ := fr_run (hRJ j hj) hrun ⟨own1_acquire, hown, own1_rel⟩ trivial
      (by show (σ "lk").toNat ≠ j; rw [hσ]; exact Ne.symm e) ⟨S, H, hl, hidj, hJj⟩ ⟨S', H', hrb⟩
    rw [hrb] at hl4
    simp only [Option.some.injEq, Prod.mk.injEq] at hl4; obtain ⟨rfl, rfl⟩ := hl4
    exact ⟨hid4, hJ4⟩

/-! ## The code -/

/-- The CPU of the thread in `r`. -/
def ownE : Expr := .bin .mod (.var "r") (.const (v NCPU))

/-- **`wakeup(i)` on CPU `c`.** -/
def wakeS (np c sb pb i : Nat) : Stmt APrim :=
  .seq (.assign "lk" (.const (v (sb + i))))
  (.seq (.seq acquireA (.seq (deQS np) relA))
  (.seq (.assign "rd" (.const (v np)))
  (.ite (.bin .ne (.var "r") (.const (v np)))
    (.ite (.bin .eq ownE (.const (v c)))
      (.assign "rd" (.var "r"))
      (.seq (.assign "pi" (.var "r")) (.seq (.assign "lk" (.bin .add (.const (v pb)) ownE))
        (.seq acquireA (.seq (enQS np) relA)))))
    .skip)))

/-- The locks `wakeup(i)` uses: sleeping queue `i` and every pending queue. -/
def wls (sb i pb : Nat) (j : Nat) : Prop := j = sb + i ∨ ∃ d < NCPU, j = pb + d

theorem own_eval {σ : Locals} {t : Nat} (hr : σ "r" = v t) (ht : t < 2 ^ 32) :
    ownE.eval σ = v (t % NCPU) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ownE, Expr.eval, BinOp.eval, hr, BitVec.toNat_umod, BitVec.toNat_ofNat, NCPU]
  rw [Nat.mod_eq_of_lt ht]; simp only [Nat.reducePow, Nat.reduceMod]; omega

theorem ne_eval {σ : Locals} {t np : Nat} (hr : σ "r" = v t) (ht : t < 2 ^ 32) (hnp : np < 2 ^ 32) :
    (Expr.bin .ne (.var "r") (.const (v np))).eval σ = 0 ↔ t = np := by
  show (if σ "r" = v np then 0 else 1) = 0 ↔ t = np
  rw [hr]
  constructor
  · intro h
    by_cases e : (v t) = (v np)
    · exact vinj ht hnp e
    · rw [if_neg e] at h; exact absurd h (by decide)
  · intro h; subst h; simp

theorem eq_eval {σ : Locals} {t c : Nat} (hr : σ "r" = v t) (ht : t < 2 ^ 32) (hc : c < NCPU) :
    (Expr.bin .eq ownE (.const (v c))).eval σ = 0 ↔ t % NCPU ≠ c := by
  show (if ownE.eval σ = v c then 1 else 0) = 0 ↔ _
  rw [own_eval hr ht]
  have hm : t % NCPU < NCPU := Nat.mod_lt _ (by decide)
  have hN : NCPU = 8 := rfl
  constructor
  · intro h e; rw [e, if_pos rfl] at h; exact absurd h (by decide)
  · intro h; rw [if_neg]; intro e; exact h (vinj (by omega) (by omega) e)

theorem lock_eval {σ : Locals} {t pb : Nat} (hr : σ "r" = v t) (ht : t < 2 ^ 32) (hpb : pb + NCPU < 2 ^ 32) :
    ((Expr.bin .add (.const (v pb)) ownE).eval σ).toNat = pb + t % NCPU := by
  show ((v pb) + ownE.eval σ).toNat = _
  rw [own_eval hr ht, BitVec.toNat_add, toNat_v (by omega), toNat_v (by have := Nat.mod_lt t (show NCPU > 0 by decide); omega)]
  have := Nat.mod_lt t (show NCPU > 0 by decide)
  exact Nat.mod_eq_of_lt (by omega)

/-! ## The run -/

/-- **The run of `wakeup(i)`** on CPU `c`, from a log on which `c` is idle on
the sleeping queue's lock and every pending queue's lock (`Rdy`). See the
module docstring. -/
theorem wake_code {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {np sb pb i : Nat}
    (hnp : 2 * np + 4 < 2 ^ 32) (hsb : sb + i < 2 ^ 32) (hpb : pb + NCPU < 2 ^ 32)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : ∀ j tn, LockArray.FairA ε c j tn bound)
    (hRJ : ∀ j, wls sb i pb j → RelyJ εR c j (Q np).J)
    (hR : Rdy np c (wls sb i pb) S H) (σ : Locals) :
    ∃ Ha : HLogR, (Q np).J (hmemR (sb + i) Ha) ∧
      ∀ h1, (Q np).rep ((Q np).replay h1) (hmemR (sb + i) Ha) → (Q np).replay h1 ≠ none →
        (¬ (taken np c h1 ≠ np ∧ taken np c h1 % NCPU ≠ c) →
          ∃ (σ' : Locals) (rb : RLog) (S' : RState) (H' : HLogR),
            Star (rprimsA εR c) ⟨wakeS np c sb pb i, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
            rreplay rb = some (S', H') ∧ Rdy np c (wls sb i pb) S' H' ∧
            (Q np).rep ((Q np).replay ((c, .deQ) :: h1)) (hmemR (sb + i) H') ∧
            σ' "rd" = v (if taken np c h1 = np then np else taken np c h1)) ∧
        (taken np c h1 ≠ np ∧ taken np c h1 % NCPU ≠ c →
          ∃ Hb : HLogR, (Q np).J (hmemR (pb + taken np c h1 % NCPU) Hb) ∧
            ∀ h2, (Q np).rep ((Q np).replay h2) (hmemR (pb + taken np c h1 % NCPU) Hb) →
              ∃ (σ' : Locals) (rb : RLog) (S' : RState) (H' : HLogR) (rm : RLog) (Sm : RState) (Hm : HLogR)
                (ys : RLog),
                Star (rprimsA εR c) ⟨wakeS np c sb pb i, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
                rreplay rb = some (S', H') ∧ Rdy np c (wls sb i pb) S' H' ∧
                (Q np).rep ((Q np).replay ((c, .enQ (taken np c h1)) :: h2))
                  (hmemR (pb + taken np c h1 % NCPU) H') ∧
                rreplay rm = some (Sm, Hm) ∧ (Q np).rep ((Q np).replay ((c, .deQ) :: h1)) (hmemR (sb + i) Hm) ∧
                rb = ys ++ rm ∧ σ' "rd" = v np) := by
  have hnp' : np < 2 ^ 32 := by omega
  let σ0 := σ.set "lk" (v (sb + i))
  have hlk0 : σ0 "lk" = v (sb + i) := Locals.set_same _ _ _
  have hiv : (v (sb + i) : Val).toNat = sb + i := toNat_v hsb
  have hR0 := hR (sb + i) (.inl rfl)
  obtain ⟨Ha, hJa, k1⟩ := deQ_atomic hE hRR hc hRA hl (by rw [hiv]; exact hR0.1) bound K hK (hF _ _) hnp σ0
    hlk0 (by rw [hiv]; exact hRJ _ (.inl rfl)) (by rw [hiv]; exact hR0.2)
  rw [hiv] at hJa
  refine ⟨Ha, hJa, fun h1 hM1 hG => ?_⟩
  obtain ⟨σ1, rm, Sm, Hm, hrun1, hlm, hidm, hMm, hJm, hres1⟩ := k1 h1 (by rw [hiv]; exact hM1)
  obtain ⟨q, hq⟩ : ∃ q, (Q np).replay h1 = some q := by
    cases h' : (Q np).replay h1 with
    | none => exact absurd h' hG
    | some q => exact ⟨q, rfl⟩
  have hr1 : σ1 "r" = v (taken np c h1) := hres1 _ (taken_result hq)
  have htle : taken np c h1 ≤ np := taken_le hq
  have ht32 : taken np c h1 < 2 ^ 32 := by omega
  have hRm : Rdy np c (wls sb i pb) Sm Hm := rdy_frame hRJ hrun1 (own1_deQS np) hlk0 hl hlm hR hidm hJm
  rw [hiv] at hMm
  let σ1' := σ1.set "rd" (v np)
  have hr1' : σ1' "r" = v (taken np c h1) := by
    show (σ1.set "rd" (v np)) "r" = _; rw [Locals.set_other _ _ (by decide)]; exact hr1
  have pre : ∀ {σf : Locals} {rf : RLog}, Runs (rprimsA εR c)
      (.ite (.bin .ne (.var "r") (.const (v np)))
        (.ite (.bin .eq ownE (.const (v c)))
          (.assign "rd" (.var "r"))
          (.seq (.assign "pi" (.var "r")) (.seq (.assign "lk" (.bin .add (.const (v pb)) ownE))
            (.seq acquireA (.seq (enQS np) relA)))))
        .skip) σ1' rm σf rf →
      Star (rprimsA εR c) ⟨wakeS np c sb pb i, .stop, σ, l⟩ ⟨.skip, .stop, σf, rf⟩ := fun hite =>
    (Runs.seq (Runs.assign _ _) (Runs.seq (Runs.of_stop hrun1) (Runs.seq (Runs.assign _ _) hite))) .stop
  refine ⟨fun hno => ?_, fun ⟨htn, hto⟩ => ?_⟩
  · by_cases htn : taken np c h1 = np
    · refine ⟨σ1', rm, Sm, Hm, pre (Runs.ite_false ((ne_eval hr1' ht32 hnp').mpr htn) Runs.skip), hlm, hRm, hMm, ?_⟩
      rw [if_pos htn]; exact Locals.set_same _ _ _
    · have hto : taken np c h1 % NCPU = c := Classical.byContradiction fun h => hno ⟨htn, h⟩
      have hne : ¬ (Expr.bin .ne (.var "r") (.const (v np))).eval σ1' = 0 := fun h =>
        htn ((ne_eval hr1' ht32 hnp').mp h)
      have heq : ¬ (Expr.bin .eq ownE (.const (v c))).eval σ1' = 0 := fun h =>
        (eq_eval hr1' ht32 hc).mp h hto
      refine ⟨σ1'.set "rd" (σ1' "r"), rm, Sm, Hm,
        pre (Runs.ite_true hne (Runs.ite_true heq (Runs.assign _ _))), hlm, hRm, hMm, ?_⟩
      rw [if_neg htn, Locals.set_same]; exact hr1'
  · have hne : ¬ (Expr.bin .ne (.var "r") (.const (v np))).eval σ1' = 0 := fun h =>
      htn ((ne_eval hr1' ht32 hnp').mp h)
    have heq : (Expr.bin .eq ownE (.const (v c))).eval σ1' = 0 := (eq_eval hr1' ht32 hc).mpr hto
    let σ2 := σ1'.set "pi" (σ1' "r")
    have hr2 : σ2 "r" = v (taken np c h1) := by
      show (σ1'.set "pi" (σ1' "r")) "r" = _; rw [Locals.set_other _ _ (by decide)]; exact hr1'
    let jv := (Expr.bin .add (.const (v pb)) ownE).eval σ2
    let σ3 := σ2.set "lk" jv
    have hjv : jv.toNat = pb + taken np c h1 % NCPU := lock_eval hr2 ht32 hpb
    have hd : taken np c h1 % NCPU < NCPU := Nat.mod_lt _ (by decide)
    have hwd : wls sb i pb (pb + taken np c h1 % NCPU) := .inr ⟨_, hd, rfl⟩
    have hRd := hRm _ hwd
    have hpi : σ3 "pi" = v (taken np c h1) := by
      show (σ2.set "lk" jv) "pi" = _
      rw [Locals.set_other _ _ (by decide)]
      show (σ1'.set "pi" (σ1' "r")) "pi" = _
      rw [Locals.set_same]; exact hr1'
    obtain ⟨Hb, hJb, k2⟩ := enQ_atomic hE hRR hc hRA hlm (by rw [hjv]; exact hRd.1) bound K hK (hF _ _) hnp
      (taken np c h1) σ3 (Locals.set_same _ _ _) hpi (by rw [hjv]; exact hRJ _ hwd) (by rw [hjv]; exact hRd.2)
    rw [hjv] at hJb
    refine ⟨Hb, hJb, fun h2 hM2 => ?_⟩
    obtain ⟨σf, rf, S5, H5, hrun2, hl5, hid5, hM5, hJ5, -⟩ := k2 h2 (by rw [hjv]; exact hM2)
    have hR5 : Rdy np c (wls sb i pb) S5 H5 :=
      rdy_frame hRJ hrun2 (own1_enQS np) (Locals.set_same _ _ _) hlm hl5 hRm hid5 hJ5
    rw [hjv] at hM5
    obtain ⟨ys, hys⟩ := own1_star_ext hrun2 ⟨own1_acquire, own1_enQS np, own1_rel⟩ trivial
    have hrd : σf "rd" = σ3 "rd" := Runs.frame (Runs.of_stop hrun2) (z := "rd")
      (by simp [frS, acquireA, loopA, enQS, MC2Queue.wr, relA])
    refine ⟨σf, rf, S5, H5, rm, Sm, Hm, ys,
      pre (Runs.ite_true hne (Runs.ite_false heq
        (Runs.seq (Runs.assign _ _) (Runs.seq (Runs.assign _ _) (Runs.of_stop hrun2))))),
      hl5, hR5, hM5, hlm, hMm, hys, ?_⟩
    rw [hrd]
    show (σ2.set "lk" jv) "rd" = _
    rw [Locals.set_other _ _ (by decide)]
    show (σ1'.set "pi" (σ1' "r")) "rd" = _
    rw [Locals.set_other _ _ (by decide)]
    exact Locals.set_same _ _ _

/-! ## Against the abstract steps -/

/-- The thread the code dequeues is the one `MC2Sched.wake1` takes. -/
theorem taken_qres (np : Nat) (c : CPU) (ql : List (MC2Sched.QId × Nat × QOp)) (q : MC2Sched.QId) :
    taken np c (MC2Sched.proj q ql) = MC2Sched.qres np ql q :=
  (MC2Sched.qres_result np ql q c).symm

end MC2Wake
