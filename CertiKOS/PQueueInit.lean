import CertiKOS.PQueueIntro

/-!
# mCertiKOS `PQueueInit`: the queue operations, ported

`enqueue`, `dequeue` and `queue_rmv` on the doubly linked thread queues.

Ported from `proc/PQueueIntro.v`: `enqueue_spec`, `dequeue_spec`. Ported from
`objects/ObjQueue.v`: `queue_rmv_spec`. Ported from
`layerlib/AuxStateDataType.v`: `TCBCorrect_range`, `TDQCorrect_range`,
`Queue_arg` (inlined).

Ported from `proc/PQueueIntroCSource.v`: the C code of the three functions.

* `enqueue_triple`, `dequeue_triple`, `queueRmv_triple`: **each function
  refines its specification.** The code is run through the steps of the layer
  below (`getTailQ`, `setNextQ`, …), never through the region.
* `enqueue_keeps`, `dequeue_keeps`, `queueRmv_keeps`: the specifications keep
  `TCBCorrect_range` and `TDQCorrect_range` (`enqueue_inv`, `dequeue_inv`,
  `queue_rmv_inv` of `proc/PQueueInit.v`).
* `real_tcb_correct`, `real_tdq_correct`: initialisation establishes them.

As in mCertiKOS, `dequeue` and `queue_rmv` need `TCBCorrect_range`: it is
what puts the `next` and `prev` they follow inside the pool. `enqueue` does
not: its specification checks the tail itself.

What differs: `dequeue` leaves its result in the local `proc_index` (the C
code ends `return proc_index;`).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PQueue

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval while_inv)

/-! ## Specifications -/

section Specs
variable (num_proc num_chan : Nat)

/-- **`enqueue_spec`**: thread `i` goes to the tail of queue `n`. -/
def enqueue_spec (n i : Nat) (d : QData) : Option QData :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc then
    match d.tdq n with
    | .TDQUndef => none
    | .TDQValid h t =>
      match d.tcb i with
      | .TCBUndef => none
      | .TCBValid st _ _ =>
        if t = num_proc then
          some { d with
            tcb := setAt d.tcb i (.TCBValid st num_proc num_proc)
            tdq := setAt d.tdq n (.TDQValid i i) }
        else if t < num_proc then
          match d.tcb t with
          | .TCBUndef => none
          | .TCBValid st' prev' _ =>
            some { d with
              tcb := setAt (setAt d.tcb t (.TCBValid st' prev' i)) i (.TCBValid st t num_proc)
              tdq := setAt d.tdq n (.TDQValid h i) }
        else none
  else none

/-- **`dequeue_spec`**: the head of queue `n` leaves it. `num_proc` if the
queue is empty. -/
def dequeue_spec (n : Nat) (d : QData) : Option (QData × Nat) :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan then
    match d.tdq n with
    | .TDQUndef => none
    | .TDQValid h t =>
      if h = num_proc then some (d, num_proc)
      else if h < num_proc then
        match d.tcb h with
        | .TCBUndef => none
        | .TCBValid _ _ next =>
          if next = num_proc then
            some ({ d with tdq := setAt d.tdq n (.TDQValid num_proc num_proc) }, h)
          else
            match d.tcb next with
            | .TCBUndef => none
            | .TCBValid st' _ next' =>
              some ({ d with
                tcb := setAt d.tcb next (.TCBValid st' num_proc next')
                tdq := setAt d.tdq n (.TDQValid next t) }, h)
      else none
  else none

/-- **`queue_rmv_spec`**: thread `i` leaves queue `n`, wherever it is in it. -/
def queue_rmv_spec (n i : Nat) (d : QData) : Option QData :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc then
    match d.tcb i with
    | .TCBUndef => none
    | .TCBValid _ prev next =>
      match d.tdq n with
      | .TDQUndef => none
      | .TDQValid h t =>
        if prev = num_proc then
          if next = num_proc then
            some { d with tdq := setAt d.tdq n (.TDQValid num_proc num_proc) }
          else
            match d.tcb next with
            | .TCBUndef => none
            | .TCBValid st1 _ next1 =>
              some { d with
                tcb := setAt d.tcb next (.TCBValid st1 num_proc next1)
                tdq := setAt d.tdq n (.TDQValid next t) }
        else
          match d.tcb prev with
          | .TCBUndef => none
          | .TCBValid st0 prev0 _ =>
            if next = num_proc then
              some { d with
                tcb := setAt d.tcb prev (.TCBValid st0 prev0 num_proc)
                tdq := setAt d.tdq n (.TDQValid h prev) }
            else
              match d.tcb next with
              | .TCBUndef => none
              | .TCBValid st1 _ next1 =>
                some { d with
                  tcb := setAt (setAt d.tcb prev (.TCBValid st0 prev0 next)) next (.TCBValid st1 prev next1) }
  else none

end Specs

/-! ## The invariants (`AuxStateDataType.v`) -/

/-- `TCBCorrect`: a valid block whose links are inside `0 … num_proc`. -/
def TCBCorrect (num_proc : Nat) : TCB → Prop
  | .TCBUndef => False
  | .TCBValid _ p nx => p ≤ num_proc ∧ nx ≤ num_proc

def TCBCorrect_range (num_proc : Nat) (t : TCBPool) : Prop := ∀ i, i < num_proc → TCBCorrect num_proc (t i)

/-- `TDQCorrect`. -/
def TDQCorrect (num_proc : Nat) : TDQueue → Prop
  | .TDQUndef => False
  | .TDQValid h t => h ≤ num_proc ∧ t ≤ num_proc

def TDQCorrect_range (num_proc num_chan : Nat) (q : TDQueuePool) : Prop :=
  ∀ i, i ≤ num_chan → TDQCorrect num_proc (q i)

section Inv
variable {num_proc num_chan : Nat}

theorem tcbc_get {t : TCBPool} (h : TCBCorrect_range num_proc t) {i : Nat} (hi : i < num_proc)
    {ts : ThreadState} {p nx : Nat} (he : t i = .TCBValid ts p nx) : p ≤ num_proc ∧ nx ≤ num_proc := by
  have := h i hi; rw [he] at this; exact this

theorem tcbc_set {t : TCBPool} (h : TCBCorrect_range num_proc t) (i : Nat) {ts : ThreadState} {p nx : Nat}
    (hp : p ≤ num_proc) (hnx : nx ≤ num_proc) : TCBCorrect_range num_proc (setAt t i (.TCBValid ts p nx)) := by
  intro j hj
  by_cases e : j = i
  · subst e; rw [setAt_eq]; exact ⟨hp, hnx⟩
  · rw [setAt_ne _ _ e]; exact h j hj

theorem tdqc_get {q : TDQueuePool} (h : TDQCorrect_range num_proc num_chan q) {i : Nat} (hi : i ≤ num_chan)
    {hd tl : Nat} (he : q i = .TDQValid hd tl) : hd ≤ num_proc ∧ tl ≤ num_proc := by
  have := h i hi; rw [he] at this; exact this

theorem tdqc_set {q : TDQueuePool} (h : TDQCorrect_range num_proc num_chan q) (i : Nat) {hd tl : Nat}
    (hh : hd ≤ num_proc) (ht : tl ≤ num_proc) :
    TDQCorrect_range num_proc num_chan (setAt q i (.TDQValid hd tl)) := by
  intro j hj
  by_cases e : j = i
  · subst e; rw [setAt_eq]; exact ⟨hh, ht⟩
  · rw [setAt_ne _ _ e]; exact h j hj

theorem init_zmap_inside {α : Type} (x : α) (f : Nat → α) : ∀ n i, i < n → init_zmap n x f i = x
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | n + 1, i, h => by
    show setAt (init_zmap n x f) n x i = x
    by_cases e : i = n
    · subst e; exact setAt_eq _ _ _
    · rw [setAt_ne _ _ e]; exact init_zmap_inside x f n i (by omega)

/-- `real_TCB_valid`. -/
theorem real_tcb_correct (t : TCBPool) : TCBCorrect_range num_proc (real_tcb num_proc t) := by
  intro i hi
  unfold real_tcb
  rw [init_zmap_inside _ _ _ _ hi]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- `real_TDQ_correct`. -/
theorem real_tdq_correct (q : TDQueuePool) : TDQCorrect_range num_proc num_chan (real_tdq num_proc num_chan q) := by
  intro i hi
  unfold real_tdq
  rw [init_zmap_inside _ _ _ _ (by omega)]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **`enqueue_spec` keeps the invariants** (`enqueue_inv`). -/
theorem enqueue_keeps {n i : Nat} {d d' : QData} (hs : enqueue_spec num_proc num_chan n i d = some d')
    (hT : TCBCorrect_range num_proc d.tcb) (hQ : TDQCorrect_range num_proc num_chan d.tdq) :
    TCBCorrect_range num_proc d'.tcb ∧ TDQCorrect_range num_proc num_chan d'.tdq := by
  unfold enqueue_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn, hi⟩ := hc
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      cases hti : d.tcb i with
      | TCBUndef => rw [hq, hti] at hs; cases hs
      | TCBValid st p nx =>
        rw [hq, hti] at hs
        simp only at hs
        obtain ⟨hh, -⟩ := tdqc_get hQ hn hq
        by_cases ht : t = num_proc
        · rw [if_pos ht] at hs
          simp only [Option.some.injEq] at hs; subst hs
          exact ⟨tcbc_set hT i (Nat.le_refl _) (Nat.le_refl _), tdqc_set hQ n (by omega) (by omega)⟩
        · rw [if_neg ht] at hs
          by_cases ht2 : t < num_proc
          · rw [if_pos ht2] at hs
            cases htt : d.tcb t with
            | TCBUndef => rw [htt] at hs; cases hs
            | TCBValid st' p' nx' =>
              rw [htt] at hs
              simp only [Option.some.injEq] at hs; subst hs
              obtain ⟨hp', -⟩ := tcbc_get hT ht2 htt
              exact ⟨tcbc_set (tcbc_set hT t hp' (by omega)) i (by omega) (Nat.le_refl _),
                tdqc_set hQ n hh (by omega)⟩
          · rw [if_neg ht2] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`dequeue_spec` keeps the invariants** (`dequeue_inv`). -/
theorem dequeue_keeps {n r : Nat} {d d' : QData} (hs : dequeue_spec num_proc num_chan n d = some (d', r))
    (hT : TCBCorrect_range num_proc d.tcb) (hQ : TDQCorrect_range num_proc num_chan d.tdq) :
    TCBCorrect_range num_proc d'.tcb ∧ TDQCorrect_range num_proc num_chan d'.tdq ∧ r ≤ num_proc := by
  unfold dequeue_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      rw [hq] at hs
      simp only at hs
      obtain ⟨-, htl⟩ := tdqc_get hQ hn hq
      by_cases hh : h = num_proc
      · rw [if_pos hh] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨hT, hQ, Nat.le_refl _⟩
      · rw [if_neg hh] at hs
        by_cases hh2 : h < num_proc
        · rw [if_pos hh2] at hs
          cases hth : d.tcb h with
          | TCBUndef => rw [hth] at hs; cases hs
          | TCBValid sth ph nxh =>
            rw [hth] at hs
            simp only at hs
            obtain ⟨-, hnx⟩ := tcbc_get hT hh2 hth
            by_cases hx : nxh = num_proc
            · rw [if_pos hx] at hs
              simp only [Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨rfl, rfl⟩ := hs
              exact ⟨hT, tdqc_set hQ n (Nat.le_refl _) (Nat.le_refl _), by omega⟩
            · rw [if_neg hx] at hs
              cases htn : d.tcb nxh with
              | TCBUndef => rw [htn] at hs; cases hs
              | TCBValid st' p' nx' =>
                rw [htn] at hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨rfl, rfl⟩ := hs
                obtain ⟨-, hnx'⟩ := tcbc_get hT (show nxh < num_proc by omega) htn
                exact ⟨tcbc_set hT nxh (Nat.le_refl _) hnx', tdqc_set hQ n hnx htl, by omega⟩
        · rw [if_neg hh2] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`queue_rmv_spec` keeps the invariants** (`queue_rmv_inv`). -/
theorem queueRmv_keeps {n i : Nat} {d d' : QData} (hs : queue_rmv_spec num_proc num_chan n i d = some d')
    (hT : TCBCorrect_range num_proc d.tcb) (hQ : TDQCorrect_range num_proc num_chan d.tdq) :
    TCBCorrect_range num_proc d'.tcb ∧ TDQCorrect_range num_proc num_chan d'.tdq := by
  unfold queue_rmv_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn, hi⟩ := hc
    cases hti : d.tcb i with
    | TCBUndef => rw [hti] at hs; cases hs
    | TCBValid st pv nx =>
      cases hq : d.tdq n with
      | TDQUndef => rw [hti, hq] at hs; cases hs
      | TDQValid h t =>
        rw [hti, hq] at hs
        simp only at hs
        obtain ⟨hpv, hnx⟩ := tcbc_get hT hi hti
        obtain ⟨hh, htl⟩ := tdqc_get hQ hn hq
        by_cases h1 : pv = num_proc
        · rw [if_pos h1] at hs
          by_cases h2 : nx = num_proc
          · rw [if_pos h2] at hs
            simp only [Option.some.injEq] at hs; subst hs
            exact ⟨hT, tdqc_set hQ n (Nat.le_refl _) (Nat.le_refl _)⟩
          · rw [if_neg h2] at hs
            cases htn : d.tcb nx with
            | TCBUndef => rw [htn] at hs; cases hs
            | TCBValid st1 p1 nx1 =>
              rw [htn] at hs
              simp only [Option.some.injEq] at hs; subst hs
              obtain ⟨-, hnx1⟩ := tcbc_get hT (show nx < num_proc by omega) htn
              exact ⟨tcbc_set hT nx (Nat.le_refl _) hnx1, tdqc_set hQ n hnx htl⟩
        · rw [if_neg h1] at hs
          cases htp : d.tcb pv with
          | TCBUndef => rw [htp] at hs; cases hs
          | TCBValid st0 p0 nx0 =>
            rw [htp] at hs
            simp only at hs
            obtain ⟨hp0, -⟩ := tcbc_get hT (show pv < num_proc by omega) htp
            by_cases h2 : nx = num_proc
            · rw [if_pos h2] at hs
              simp only [Option.some.injEq] at hs; subst hs
              exact ⟨tcbc_set hT pv hp0 (Nat.le_refl _), tdqc_set hQ n hh hpv⟩
            · rw [if_neg h2] at hs
              cases htn : d.tcb nx with
              | TCBUndef => rw [htn] at hs; cases hs
              | TCBValid st1 p1 nx1 =>
                rw [htn] at hs
                simp only [Option.some.injEq] at hs; subst hs
                obtain ⟨-, hnx1⟩ := tcbc_get hT (show nx < num_proc by omega) htn
                exact ⟨tcbc_set (tcbc_set hT pv hp0 hnx) nx hpv hnx1, hQ⟩
  · rw [if_neg hc] at hs; cases hs

end Inv

/-! ## The C code (`PQueueIntroCSource.v`) -/

/-- ```
tail = get_tail(chan_index);
if (tail == num_proc) {
  set_prev(proc_index, num_proc); set_next(proc_index, num_proc);
  set_head(chan_index, proc_index); set_tail(chan_index, proc_index);
} else {
  set_next(tail, proc_index); set_prev(proc_index, tail);
  set_next(proc_index, num_proc); set_tail(chan_index, proc_index);
}
``` -/
def enqueueS (tb qb num_proc : Nat) : Stmt APrim :=
  .seq (getTailS qb "tail" (.var "chan_index"))
    (.ite (.bin .eq (.var "tail") (.const (BitVec.ofNat 32 num_proc)))
      (.seq (setPrevS tb (.var "proc_index") (.const (BitVec.ofNat 32 num_proc)))
        (.seq (setNextS tb (.var "proc_index") (.const (BitVec.ofNat 32 num_proc)))
          (.seq (setHeadS qb (.var "chan_index") (.var "proc_index"))
            (setTailS qb (.var "chan_index") (.var "proc_index")))))
      (.seq (setNextS tb (.var "tail") (.var "proc_index"))
        (.seq (setPrevS tb (.var "proc_index") (.var "tail"))
          (.seq (setNextS tb (.var "proc_index") (.const (BitVec.ofNat 32 num_proc)))
            (setTailS qb (.var "chan_index") (.var "proc_index"))))))

/-- ```
proc_index = num_proc;
head = get_head(chan_index);
if (head != num_proc) {
  proc_index = head;
  next = get_next(head);
  if (next == num_proc) { set_head(chan_index, num_proc); set_tail(chan_index, num_proc); }
  else { set_prev(next, num_proc); set_head(chan_index, next); }
}
return proc_index;
``` -/
def dequeueS (tb qb num_proc : Nat) : Stmt APrim :=
  .seq (.assign "proc_index" (.const (BitVec.ofNat 32 num_proc)))
    (.seq (getHeadS qb "head" (.var "chan_index"))
      (.ite (.bin .ne (.var "head") (.const (BitVec.ofNat 32 num_proc)))
        (.seq (.assign "proc_index" (.var "head"))
          (.seq (getNextS tb "next" (.var "head"))
            (.ite (.bin .eq (.var "next") (.const (BitVec.ofNat 32 num_proc)))
              (.seq (setHeadS qb (.var "chan_index") (.const (BitVec.ofNat 32 num_proc)))
                (setTailS qb (.var "chan_index") (.const (BitVec.ofNat 32 num_proc))))
              (.seq (setPrevS tb (.var "next") (.const (BitVec.ofNat 32 num_proc)))
                (setHeadS qb (.var "chan_index") (.var "next"))))))
        .skip))

/-- ```
prev = get_prev(proc_index);
next = get_next(proc_index);
if (prev == num_proc) {
  if (next == num_proc) { set_head(chan_index, num_proc); set_tail(chan_index, num_proc); }
  else { set_prev(next, num_proc); set_head(chan_index, next); }
} else {
  if (next == num_proc) { set_next(prev, num_proc); set_tail(chan_index, prev); }
  else { if (prev != next) set_next(prev, next); set_prev(next, prev); }
}
``` -/
def queueRmvS (tb qb num_proc : Nat) : Stmt APrim :=
  .seq (getPrevS tb "prev" (.var "proc_index"))
    (.seq (getNextS tb "next" (.var "proc_index"))
      (.ite (.bin .eq (.var "prev") (.const (BitVec.ofNat 32 num_proc)))
        (.ite (.bin .eq (.var "next") (.const (BitVec.ofNat 32 num_proc)))
          (.seq (setHeadS qb (.var "chan_index") (.const (BitVec.ofNat 32 num_proc)))
            (setTailS qb (.var "chan_index") (.const (BitVec.ofNat 32 num_proc))))
          (.seq (setPrevS tb (.var "next") (.const (BitVec.ofNat 32 num_proc)))
            (setHeadS qb (.var "chan_index") (.var "next"))))
        (.ite (.bin .eq (.var "next") (.const (BitVec.ofNat 32 num_proc)))
          (.seq (setNextS tb (.var "prev") (.const (BitVec.ofNat 32 num_proc)))
            (setTailS qb (.var "chan_index") (.var "prev")))
          (.seq (.ite (.bin .ne (.var "prev") (.var "next")) (setNextS tb (.var "prev") (.var "next")) .skip)
            (setPrevS tb (.var "next") (.var "prev"))))))

/-- The cells this layer writes: the control blocks and the queue pool. -/
def QTF (tb num_proc qb num_chan : Nat) (k : Nat) : Prop := TF tb num_proc k ∨ QF qb num_chan k

theorem QData.ext3 {d1 d2 : QData} (h1 : d1.toSData = d2.toSData) (h2 : d1.tcb = d2.tcb)
    (h3 : d1.tdq = d2.tdq) : d1 = d2 := by
  obtain ⟨⟨s1, t1⟩, q1⟩ := d1
  obtain ⟨⟨s2, t2⟩, q2⟩ := d2
  change s1 = s2 at h1; change t1 = t2 at h2; change q1 = q2 at h3
  subst h1; subst h2; subst h3; rfl

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb : Nat}

theorem np_lt (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) : num_proc < 2 ^ 32 := by
  have := hL.tlay.hte; have := hL.tlay.slay.lay.hib; have := hL.tlay.slay.lay.hfb
  have := hL.tlay.slay.lay.hend; omega

variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MQ" => MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb
local notation "QTF'" => QTF tb num_proc qb num_chan

/-- **`enqueue` runs as `enqueue_spec` says.** -/
theorem enqueue_step (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {σ : Locals}
    {d d' : QData} {n i : Nat} (hcn : σ "chan_index" = BitVec.ofNat 32 n)
    (hpi : σ "proc_index" = BitVec.ofNat 32 i) (hs : enqueue_spec num_proc num_chan n i d = some d') :
    ∃ σ', Step εR c i0 MQ QTF' (enqueueS tb qb num_proc) σ d σ' d' := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL
  have hT : ∀ k, TF tb num_proc k → QTF tb num_proc qb num_chan k := fun _ h => Or.inl h
  have hQ : ∀ k, QF qb num_chan k → QTF tb num_proc qb num_chan k := fun _ h => Or.inr h
  unfold enqueue_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn, hi⟩ := hc
    have hi32 : i < 2 ^ 32 := by omega
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      cases hti : d.tcb i with
      | TCBUndef => rw [hq, hti] at hs; cases hs
      | TCBValid st p nx =>
        rw [hq, hti] at hs
        simp only at hs
        by_cases ht : t = num_proc
        · rw [if_pos ht] at hs
          simp only [Option.some.injEq] at hs; subst hs
          exact ⟨_, Step.cast (Step.seq (getTailQ εR c i0 hL "tail" (by decide) hcn hn hq)
            (Step.ite_true (eqc_true (by simp [Locals.set]) ht)
              (Step.seq (setPrevQ εR c i0 hL hT (by simp [Expr.eval, Locals.set, hpi]) rfl hi hnp hti)
                (Step.seq (setNextQ εR c i0 hL hT (by simp [Expr.eval, Locals.set, hpi]) rfl hi hnp
                    (setAt_eq _ _ _))
                  (Step.seq (setHeadQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn])
                      (by simp [Expr.eval, Locals.set, hpi]) hn hi32 hq)
                    (setTailQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn])
                      (by simp [Expr.eval, Locals.set, hpi]) hn hi32 (setAt_eq _ _ _)))))))
            rfl (QData.ext3 rfl (setAt_setAt _ _ _ _) (setAt_setAt _ _ _ _))⟩
        · rw [if_neg ht] at hs
          by_cases ht2 : t < num_proc
          · rw [if_pos ht2] at hs
            have ht32 : t < 2 ^ 32 := by omega
            cases htt : d.tcb t with
            | TCBUndef => rw [htt] at hs; cases hs
            | TCBValid st' p' nx' =>
              rw [htt] at hs
              simp only [Option.some.injEq] at hs; subst hs
              obtain ⟨p2, nx2, h2⟩ : ∃ p2 nx2, setAt d.tcb t (.TCBValid st' p' i) i = .TCBValid st p2 nx2 := by
                by_cases e : i = t
                · subst e
                  rw [hti] at htt; cases htt
                  exact ⟨_, _, setAt_eq _ _ _⟩
                · rw [setAt_ne _ _ e]; exact ⟨_, _, hti⟩
              exact ⟨_, Step.cast (Step.seq (getTailQ εR c i0 hL "tail" (by decide) hcn hn hq)
                (Step.ite_false (eqc_false (by simp [Locals.set]) ht32 hnp ht)
                  (Step.seq (setNextQ εR c i0 hL hT (by simp [Expr.eval, Locals.set])
                      (by simp [Expr.eval, Locals.set, hpi]) ht2 hi32 htt)
                    (Step.seq (setPrevQ εR c i0 hL hT (by simp [Expr.eval, Locals.set, hpi])
                        (by simp [Expr.eval, Locals.set]) hi ht32 h2)
                      (Step.seq (setNextQ εR c i0 hL hT (by simp [Expr.eval, Locals.set, hpi]) rfl hi hnp
                          (setAt_eq _ _ _))
                        (setTailQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn])
                          (by simp [Expr.eval, Locals.set, hpi]) hn hi32 hq))))))
                rfl (QData.ext3 rfl (setAt_setAt _ _ _ _) rfl)⟩
          · rw [if_neg ht2] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`enqueue` refines `enqueue_spec`.** -/
theorem enqueue_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (n i : Nat) :
    Triple εR c i0 MQ QTF'
      (fun σ d => σ "chan_index" = BitVec.ofNat 32 n ∧ σ "proc_index" = BitVec.ofNat 32 i ∧
        ∃ d1, enqueue_spec num_proc num_chan n i d = some d1)
      (enqueueS tb qb num_proc)
      (fun _ d _ d' => enqueue_spec num_proc num_chan n i d = some d') :=
  Step.triple (fun σ d ⟨hcn, hpi, d1, hs⟩ => by
    obtain ⟨σ', h⟩ := enqueue_step εR c i0 hL hcn hpi hs
    exact ⟨σ', d1, h, hs⟩)

/-- **`dequeue` runs as `dequeue_spec` says**, and leaves its result in
`proc_index`. -/
theorem dequeue_step (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {σ : Locals}
    {d d' : QData} {n r : Nat} (hcn : σ "chan_index" = BitVec.ofNat 32 n)
    (hI : TCBCorrect_range num_proc d.tcb) (hs : dequeue_spec num_proc num_chan n d = some (d', r)) :
    ∃ σ', Step εR c i0 MQ QTF' (dequeueS tb qb num_proc) σ d σ' d' ∧
      σ' "proc_index" = BitVec.ofNat 32 r := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL
  have hT : ∀ k, TF tb num_proc k → QTF tb num_proc qb num_chan k := fun _ h => Or.inl h
  have hQ : ∀ k, QF qb num_chan k → QTF tb num_proc qb num_chan k := fun _ h => Or.inr h
  unfold dequeue_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      rw [hq] at hs
      simp only at hs
      by_cases hh : h = num_proc
      · rw [if_pos hh] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨_, Step.seq (Step.assign "proc_index" (by decide) _)
          (Step.seq (getHeadQ εR c i0 hL "head" (by decide) (by simp [Expr.eval, Locals.set, hcn]) hn hq)
            (Step.ite_false (nec_false (by simp [Locals.set]) hh) Step.skip)),
          by simp [Expr.eval, Locals.set]⟩
      · rw [if_neg hh] at hs
        by_cases hh2 : h < num_proc
        · rw [if_pos hh2] at hs
          have hh32 : h < 2 ^ 32 := by omega
          cases hth : d.tcb h with
          | TCBUndef => rw [hth] at hs; cases hs
          | TCBValid sth ph nxh =>
            rw [hth] at hs
            simp only at hs
            obtain ⟨-, hnx⟩ := tcbc_get hI hh2 hth
            have hnx32 : nxh < 2 ^ 32 := by omega
            by_cases hx : nxh = num_proc
            · rw [if_pos hx] at hs
              simp only [Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨rfl, rfl⟩ := hs
              exact ⟨_, Step.cast (Step.seq (Step.assign "proc_index" (by decide) _)
                (Step.seq (getHeadQ εR c i0 hL "head" (by decide) (by simp [Expr.eval, Locals.set, hcn]) hn hq)
                  (Step.ite_true (nec_true (by simp [Locals.set]) hh32 hnp hh)
                    (Step.seq (Step.assign "proc_index" (by decide) _)
                      (Step.seq (getNextQ εR c i0 hL "next" (by decide) (by simp [Expr.eval, Locals.set])
                          hh2 hth)
                        (Step.ite_true (eqc_true (by simp [Locals.set]) hx)
                          (Step.seq (setHeadQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn]) rfl hn
                              hnp hq)
                            (setTailQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn]) rfl hn hnp
                              (setAt_eq _ _ _)))))))))
                rfl (QData.ext3 rfl rfl (setAt_setAt _ _ _ _)), by simp [Expr.eval, Locals.set]⟩
            · rw [if_neg hx] at hs
              have hnxlt : nxh < num_proc := by omega
              cases htn : d.tcb nxh with
              | TCBUndef => rw [htn] at hs; cases hs
              | TCBValid st' p' nx' =>
                rw [htn] at hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨rfl, rfl⟩ := hs
                exact ⟨_, Step.seq (Step.assign "proc_index" (by decide) _)
                  (Step.seq (getHeadQ εR c i0 hL "head" (by decide) (by simp [Expr.eval, Locals.set, hcn]) hn
                      hq)
                    (Step.ite_true (nec_true (by simp [Locals.set]) hh32 hnp hh)
                      (Step.seq (Step.assign "proc_index" (by decide) _)
                        (Step.seq (getNextQ εR c i0 hL "next" (by decide) (by simp [Expr.eval, Locals.set])
                            hh2 hth)
                          (Step.ite_false (eqc_false (by simp [Locals.set]) hnx32 hnp hx)
                            (Step.seq (setPrevQ εR c i0 hL hT (by simp [Expr.eval, Locals.set]) rfl hnxlt
                                hnp htn)
                              (setHeadQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn])
                                (by simp [Expr.eval, Locals.set]) hn hnx32 hq))))))),
                  by simp [Expr.eval, Locals.set]⟩
        · rw [if_neg hh2] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`dequeue` refines `dequeue_spec`.** -/
theorem dequeue_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (n : Nat) :
    Triple εR c i0 MQ QTF'
      (fun σ d => σ "chan_index" = BitVec.ofNat 32 n ∧ TCBCorrect_range num_proc d.tcb ∧
        ∃ d1 r, dequeue_spec num_proc num_chan n d = some (d1, r))
      (dequeueS tb qb num_proc)
      (fun _ d σ' d' => ∃ r, dequeue_spec num_proc num_chan n d = some (d', r) ∧
        σ' "proc_index" = BitVec.ofNat 32 r) :=
  Step.triple (fun σ d ⟨hcn, hI, d1, r, hs⟩ => by
    obtain ⟨σ', h, hr⟩ := dequeue_step εR c i0 hL hcn hI hs
    exact ⟨σ', d1, h, r, hs, hr⟩)

/-- **`queue_rmv` runs as `queue_rmv_spec` says.** -/
theorem queueRmv_step (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {σ : Locals}
    {d d' : QData} {n i : Nat} (hcn : σ "chan_index" = BitVec.ofNat 32 n)
    (hpi : σ "proc_index" = BitVec.ofNat 32 i) (hI : TCBCorrect_range num_proc d.tcb)
    (hs : queue_rmv_spec num_proc num_chan n i d = some d') :
    ∃ σ', Step εR c i0 MQ QTF' (queueRmvS tb qb num_proc) σ d σ' d' := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL
  have hT : ∀ k, TF tb num_proc k → QTF tb num_proc qb num_chan k := fun _ h => Or.inl h
  have hQ : ∀ k, QF qb num_chan k → QTF tb num_proc qb num_chan k := fun _ h => Or.inr h
  unfold queue_rmv_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn, hi⟩ := hc
    cases hti : d.tcb i with
    | TCBUndef => rw [hti] at hs; cases hs
    | TCBValid st pv nx =>
      cases hq : d.tdq n with
      | TDQUndef => rw [hti, hq] at hs; cases hs
      | TDQValid h t =>
        rw [hti, hq] at hs
        simp only at hs
        obtain ⟨hpv, hnx⟩ := tcbc_get hI hi hti
        have hpv32 : pv < 2 ^ 32 := by omega
        have hnx32 : nx < 2 ^ 32 := by omega
        have A := getPrevQ (ida := ida) εR c i0 hL (F := QTF tb num_proc qb num_chan) "prev" (by decide)
          (ie := .var "proc_index") (σ := σ) hpi hi hti
        have B := getNextQ (ida := ida) εR c i0 hL (F := QTF tb num_proc qb num_chan) "next" (by decide)
          (ie := .var "proc_index") (σ := σ.set "prev" (BitVec.ofNat 32 pv)) (d := d) (i := i)
          (by simp [Expr.eval, Locals.set, hpi]) hi hti
        by_cases h1 : pv = num_proc
        · rw [if_pos h1] at hs
          by_cases h2 : nx = num_proc
          · rw [if_pos h2] at hs
            simp only [Option.some.injEq] at hs; subst hs
            exact ⟨_, Step.cast (Step.seq A (Step.seq B
              (Step.ite_true (eqc_true (by simp [Locals.set]) h1)
                (Step.ite_true (eqc_true (by simp [Locals.set]) h2)
                  (Step.seq (setHeadQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn]) rfl hn hnp hq)
                    (setTailQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn]) rfl hn hnp
                      (setAt_eq _ _ _)))))))
              rfl (QData.ext3 rfl rfl (setAt_setAt _ _ _ _))⟩
          · rw [if_neg h2] at hs
            have hnxlt : nx < num_proc := by omega
            cases htn : d.tcb nx with
            | TCBUndef => rw [htn] at hs; cases hs
            | TCBValid st1 p1 nx1 =>
              rw [htn] at hs
              simp only [Option.some.injEq] at hs; subst hs
              exact ⟨_, Step.seq A (Step.seq B
                (Step.ite_true (eqc_true (by simp [Locals.set]) h1)
                  (Step.ite_false (eqc_false (by simp [Locals.set]) hnx32 hnp h2)
                    (Step.seq (setPrevQ εR c i0 hL hT (by simp [Expr.eval, Locals.set]) rfl hnxlt hnp htn)
                      (setHeadQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn])
                        (by simp [Expr.eval, Locals.set]) hn hnx32 hq)))))⟩
        · rw [if_neg h1] at hs
          have hpvlt : pv < num_proc := by omega
          cases htp : d.tcb pv with
          | TCBUndef => rw [htp] at hs; cases hs
          | TCBValid st0 p0 nx0 =>
            rw [htp] at hs
            simp only at hs
            by_cases h2 : nx = num_proc
            · rw [if_pos h2] at hs
              simp only [Option.some.injEq] at hs; subst hs
              exact ⟨_, Step.seq A (Step.seq B
                (Step.ite_false (eqc_false (by simp [Locals.set]) hpv32 hnp h1)
                  (Step.ite_true (eqc_true (by simp [Locals.set]) h2)
                    (Step.seq (setNextQ εR c i0 hL hT (by simp [Expr.eval, Locals.set]) rfl hpvlt hnp htp)
                      (setTailQ εR c i0 hL hQ (by simp [Expr.eval, Locals.set, hcn])
                        (by simp [Expr.eval, Locals.set]) hn hpv32 hq)))))⟩
            · rw [if_neg h2] at hs
              have hnxlt : nx < num_proc := by omega
              cases htn : d.tcb nx with
              | TCBUndef => rw [htn] at hs; cases hs
              | TCBValid st1 p1 nx1 =>
                rw [htn] at hs
                simp only [Option.some.injEq] at hs; subst hs
                by_cases h3 : pv = nx
                · exact ⟨_, Step.cast (Step.seq A (Step.seq B
                    (Step.ite_false (eqc_false (by simp [Locals.set]) hpv32 hnp h1)
                      (Step.ite_false (eqc_false (by simp [Locals.set]) hnx32 hnp h2)
                        (Step.seq (Step.ite_false (nev_false (a := pv) (b := nx) (by simp [Locals.set])
                            (by simp [Locals.set]) h3) Step.skip)
                          (setPrevQ εR c i0 hL hT (by simp [Expr.eval, Locals.set])
                            (by simp [Expr.eval, Locals.set]) hnxlt hpv32 htn))))))
                    rfl (QData.ext3 rfl (by
                      show setAt d.tcb nx _ = setAt (setAt d.tcb pv _) nx _
                      subst h3; exact (setAt_setAt _ _ _ _).symm) rfl)⟩
                · exact ⟨_, Step.seq A (Step.seq B
                    (Step.ite_false (eqc_false (by simp [Locals.set]) hpv32 hnp h1)
                      (Step.ite_false (eqc_false (by simp [Locals.set]) hnx32 hnp h2)
                        (Step.seq (Step.ite_true (nev_true (a := pv) (b := nx) (by simp [Locals.set])
                            (by simp [Locals.set]) hpv32 hnx32 h3)
                            (setNextQ εR c i0 hL hT (by simp [Expr.eval, Locals.set])
                              (by simp [Expr.eval, Locals.set]) hpvlt hnx32 htp))
                          (setPrevQ εR c i0 hL hT (by simp [Expr.eval, Locals.set])
                            (by simp [Expr.eval, Locals.set]) hnxlt hpv32
                            ((setAt_ne _ _ (fun e => h3 e.symm)).trans htn))))))⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`queue_rmv` refines `queue_rmv_spec`.** -/
theorem queueRmv_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (n i : Nat) :
    Triple εR c i0 MQ QTF'
      (fun σ d => σ "chan_index" = BitVec.ofNat 32 n ∧ σ "proc_index" = BitVec.ofNat 32 i ∧
        TCBCorrect_range num_proc d.tcb ∧ ∃ d1, queue_rmv_spec num_proc num_chan n i d = some d1)
      (queueRmvS tb qb num_proc)
      (fun _ d _ d' => queue_rmv_spec num_proc num_chan n i d = some d') :=
  Step.triple (fun σ d ⟨hcn, hpi, hI, d1, hs⟩ => by
    obtain ⟨σ', h⟩ := queueRmv_step εR c i0 hL hcn hpi hI hs
    exact ⟨σ', d1, h, hs⟩)

end Code

end PQueue
