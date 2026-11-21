import CertiKOS.MC2Atomic
import CertiKOS.PAbQueue
import CertiKOS.KernPAlloc

/-!
# mC2: the shared queues

mC2's thread queues (the sleeping queues, and each CPU's pending queue) are
**shared queues** ([PLDI18] §4.2, [OSDI16] §4): doubly linked lists, each
protected by its own lock, abstracted to lists, with the atomic events
`c.enQ i e` and `c.deQ i`. The code inside the lock is `deQ_t` (and `enQ_t`),
working on the local copy.

Here each queue is one atomic object (`MC2Atomic`) on the region of its own
lock:

* **The region of a queue**: cell 0 is the head, cell 1 the tail, and cells
  `2 + 2x`, `3 + 2x` are thread `x`'s `prev` and `next` while it is on this
  queue. `np` (the number of threads) is the empty link, as in mCertiKOS.
* `RepQ np l b`: the region `b` is the queue `l` (a list of threads, the tail
  first, as `PAbQueue` has it). The links are those of `PAbQueue.links`.
* `Q np`: the object. Its state is `some l`, or `none` once a thread already
  on the queue (or not a thread) has been enqueued: the code then corrupts
  the list. The scheduler of stage 3 must show this never happens; a
  dequeue's result on `none` is unspecified.
* `enQS`, `deQS`: mCertiKOS's `enqueue` and `dequeue` (`PQueueInit`), on the
  queue's own region.
* `enQ_impl`, `deQ_impl`: **the code implements the operations** (`Impl`), so
  by `atomic_call` each locked call is one event `(c, enQ t)` or `(c, deQ)`.

**A design decision of ours:** the papers give the abstract state (a.tcbp, a.tdqp) but not where the
links live. With one lock per queue, a thread's links are kept in the region
of the queue it is on, so no two locks protect the same cell.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MC2Queue

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region hmemR setCell)
open LockRegionCPU KernFrame Layer LogInv
open PAbQueue (links links_snoc links_mem getLastD_append headD_append)
open MC2

local notation "v" n => (BitVec.ofNat 32 n : Val)

/-! ## The representation -/

/-- **The region `b` is the queue `l`** (tail first). -/
def RepQ (np : Nat) (l : List Nat) (b : Region) : Prop :=
  l.Nodup ∧ (∀ x ∈ l, x < np) ∧ b 0 = (v (l.getLastD np)) ∧ b 1 = (v (l.headD np)) ∧
    ∀ x p nx, (x, p, nx) ∈ links np np l → b (2 + 2 * x) = (v p) ∧ b (3 + 2 * x) = (v nx)

inductive QOp
  | enQ (t : Nat)
  | deQ

/-- The operations on the abstract queue. -/
def qstep (np : Nat) : QOp → Option (List Nat) → Option (List Nat) × Option Nat
  | .enQ t, some l => if t < np ∧ t ∉ l then (some (t :: l), some 0) else (none, none)
  | .enQ _, none => (none, none)
  | .deQ, some l => (some l.dropLast, some (l.getLastD np))
  | .deQ, none => (none, none)

/-- **A shared queue, as an atomic object.** -/
def Q (np : Nat) : AObj where
  S := Option (List Nat)
  init := some []
  Op := QOp
  step := fun _ o s => qstep np o s
  rep := fun s b => match s with
    | some l => RepQ np l b
    | none => True

/-! ## The code -/

/-- Cell `k + 2x`, for `x` in a local. -/
def cE (k : Nat) (x : Ident) : Expr := .bin .add (.const (v k)) (.bin .mul (.const 2) (.var x))

def wr (je ve : Expr) : Stmt APrim := .call "_" .push [lkE, je, ve]

/-- `enqueue(pi)`: thread `pi` goes to the tail. -/
def enQS (np : Nat) : Stmt APrim :=
  .seq (.assign "r" (.const 0))
    (.seq (.call "tl" .pull [lkE, .const (v 1)])
      (.ite (.bin .eq (.var "tl") (.const (v np)))
        (.seq (wr (cE 2 "pi") (.const (v np))) (.seq (wr (cE 3 "pi") (.const (v np)))
          (.seq (wr (.const (v 0)) (.var "pi")) (wr (.const (v 1)) (.var "pi")))))
        (.seq (wr (cE 3 "tl") (.var "pi")) (.seq (wr (cE 2 "pi") (.var "tl"))
          (.seq (wr (cE 3 "pi") (.const (v np))) (wr (.const (v 1)) (.var "pi")))))))

/-- `dequeue()`: the head leaves; `np` if the queue is empty. The result is in
`r`. -/
def deQS (np : Nat) : Stmt APrim :=
  .seq (.assign "r" (.const (v np)))
    (.seq (.call "hd" .pull [lkE, .const (v 0)])
      (.ite (.bin .ne (.var "hd") (.const (v np)))
        (.seq (.assign "r" (.var "hd"))
          (.seq (.call "nx" .pull [lkE, cE 3 "hd"])
            (.ite (.bin .eq (.var "nx") (.const (v np)))
              (.seq (wr (.const (v 0)) (.const (v np))) (wr (.const (v 1)) (.const (v np))))
              (.seq (wr (cE 2 "nx") (.const (v np))) (wr (.const (v 0)) (.var "nx"))))))
        .skip))

/-! ## Helpers -/

theorem vinj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : (v a) = (v b)) : a = b := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem toNat_v {a : Nat} (ha : a < 2 ^ 32) : (v a).toNat = a := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt ha

theorem cE_eval {σ : Locals} {k : Nat} {x : Ident} {n : Nat} (h : σ x = (v n)) (hk : k + 2 * n < 2 ^ 32) :
    ((cE k x).eval σ).toNat = k + 2 * n := by
  have h2 : (2 : Val).toNat = 2 := rfl
  simp only [cE, Expr.eval, BinOp.eval, h, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h2]
  omega

theorem rd_step {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (x : Ident) (je : Expr) {j : Nat} (hj : (je.eval σ).toNat = j) :
    Runs (rprimsA εR c) (.call x .pull [lkE, je]) σ l (σ.set x (b j)) l := by
  have := cs1_rd (εR := εR) h hlk x je; rw [hj] at this; exact this

theorem wr_step {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (je ve : Expr) {j : Nat} {w : Val} (hj : (je.eval σ).toNat = j)
    (hw : ve.eval σ = w) :
    ∃ l', Runs (rprimsA εR c) (wr je ve) σ l (σ.set "_" 0) l' ∧ CS1 c i l' (setCell b j w) := by
  obtain ⟨l', r, c'⟩ := cs1_wr (εR := εR) h hlk je ve; rw [hj, hw] at c'; exact ⟨l', r, c'⟩

theorem sc_eq' (b : Region) (j : Nat) (w : Val) : setCell b j w j = w := by simp [setCell]

theorem sc_ne' {b : Region} {j k : Nat} {w : Val} (h : k ≠ j) : setCell b j w k = b k := by
  simp [setCell, h]

theorem nil_of_headD {np : Nat} {l : List Nat} (hnp : np < 2 ^ 32) (hl : ∀ x ∈ l, x < np)
    (h : (v (l.headD np)) = (v np)) : l = [] := by
  cases l with
  | nil => rfl
  | cons x r =>
    have hx := hl x List.mem_cons_self
    exact absurd (vinj (by simp only [List.headD_cons]; omega) hnp h) (by simp only [List.headD_cons]; omega)

theorem getLastD_lt {np : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < np) (hne : l ≠ []) : l.getLastD np < np := by
  rcases List.eq_nil_or_concat l with h | ⟨l', b, rfl⟩
  · exact absurd h hne
  · rw [List.concat_eq_append, getLastD_append]; exact hl b (by simp)

theorem headD_ne {np : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < np) (hne : l ≠ []) : l.headD np < np := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x r => simp only [List.headD_cons]; exact hl x List.mem_cons_self

theorem nil_of_getLastD {np : Nat} {l : List Nat} (hnp : np < 2 ^ 32) (hl : ∀ x ∈ l, x < np)
    (h : (v (l.getLastD np)) = (v np)) : l = [] := by
  by_cases hne : l = []
  · exact hne
  · have := getLastD_lt hl hne
    exact absurd (vinj (by omega) hnp h) (by omega)

/-! ## `enQ` -/

/-- **`enqueue` implements `enQ t`.** -/
theorem enQ_impl (εR : REnv) (c : CPU) (i : Nat) {np : Nat} (hnp : 2 * np + 4 < 2 ^ 32) (t : Nat) :
    Impl εR c i (Q np) (fun _ => True) (fun σ => σ "pi" = (v t)) (.enQ t) "r" (enQS np) := by
  intro σ l b d hlk hcs hM hP
  have hnp' : np < 2 ^ 32 := by omega
  let σ0 := σ.set "r" 0
  have r0 : Runs (rprimsA εR c) (.assign "r" (.const 0)) σ l σ0 l := Runs.assign _ _
  have hlk0 : (σ0 "lk").toNat = i := by simpa [σ0, Locals.set] using hlk
  have r1 := rd_step (εR := εR) hcs hlk0 "tl" (.const (v 1)) (j := 1) rfl
  let σ1 := σ0.set "tl" (b 1)
  have hlk1 : (σ1 "lk").toNat = i := by simpa [σ1, σ0, Locals.set] using hlk
  have hpi1 : σ1 "pi" = (v t) := by simp [σ1, σ0, Locals.set, hP]
  have hr1 : σ1 "r" = 0 := by simp [σ1, σ0, Locals.set]
  have htl1 : σ1 "tl" = b 1 := by simp [σ1, Locals.set]
  -- the locals after `k` writes
  have s_ne : ∀ (τ : Locals) (z : Ident), z ≠ "_" → (τ.set "_" 0) z = τ z :=
    fun τ z hz => Locals.set_other _ _ hz
  let τ1 := σ1.set "_" 0
  let τ2 := τ1.set "_" 0
  let τ3 := τ2.set "_" 0
  let τ4 := τ3.set "_" 0
  have L1 : ∀ z, z ≠ "_" → τ1 z = σ1 z := fun z hz => s_ne σ1 z hz
  have L2 : ∀ z, z ≠ "_" → τ2 z = σ1 z := fun z hz => (s_ne τ1 z hz).trans (L1 z hz)
  have L3 : ∀ z, z ≠ "_" → τ3 z = σ1 z := fun z hz => (s_ne τ2 z hz).trans (L2 z hz)
  have L4 : ∀ z, z ≠ "_" → τ4 z = σ1 z := fun z hz => (s_ne τ3 z hz).trans (L3 z hz)
  have hlkτ1 : (τ1 "lk").toNat = i := by rw [L1 _ (by decide)]; exact hlk1
  have hlkτ2 : (τ2 "lk").toNat = i := by rw [L2 _ (by decide)]; exact hlk1
  have hlkτ3 : (τ3 "lk").toNat = i := by rw [L3 _ (by decide)]; exact hlk1
  have hlk4 : τ4 "lk" = σ "lk" := by rw [L4 _ (by decide)]; simp [σ1, σ0, Locals.set]
  have hr4 : τ4 "r" = 0 := by rw [L4 _ (by decide)]; exact hr1
  have hR0 : ∀ r, (qstep np (.enQ t) d).2 = some r → τ4 "r" = (v r) := by
    intro r hr
    cases d with
    | none => simp [qstep] at hr
    | some l0 =>
      by_cases hg : t < np ∧ t ∉ l0
      · simp only [qstep, if_pos hg, Option.some.injEq] at hr; subst hr; rw [hr4]; rfl
      · simp only [qstep, if_neg hg] at hr; cases hr
  by_cases hte : b 1 = (v np)
  · -- the queue is empty
    have hc : ¬ (Expr.bin .eq (.var "tl") (.const (v np))).eval σ1 = 0 := by
      simp [Expr.eval, BinOp.eval, htl1, hte]
    obtain ⟨l2, w1, c2⟩ := wr_step (εR := εR) hcs hlk1 (cE 2 "pi") (.const (v np)) (j := ((cE 2 "pi").eval σ1).toNat) (w := (v np))
      rfl rfl
    obtain ⟨l3, w2, c3⟩ := wr_step (εR := εR) c2 hlkτ1 (cE 3 "pi") (.const (v np))
      (j := ((cE 3 "pi").eval σ1).toNat) (w := (v np)) (by simp [cE, Expr.eval, L1 "pi" (by decide)]) rfl
    obtain ⟨l4, w3, c4⟩ := wr_step (εR := εR) c3 hlkτ2 (.const (v 0)) (.var "pi") (j := 0) rfl
      (show τ2 "pi" = (v t) by rw [L2 _ (by decide)]; exact hpi1)
    obtain ⟨l5, w4, c5⟩ := wr_step (εR := εR) c4 hlkτ3 (.const (v 1)) (.var "pi") (j := 1) rfl
      (show τ3 "pi" = (v t) by rw [L3 _ (by decide)]; exact hpi1)
    refine ⟨τ4, l5, _, (qstep np (.enQ t) d).1,
      Runs.seq r0 (Runs.seq r1 (Runs.ite_true hc (Runs.seq w1 (Runs.seq w2 (Runs.seq w3 w4))))), c5, ?_, hlk4,
      fun k hk => absurd trivial hk, rfl, hR0⟩
    cases d with
    | none => trivial
    | some l0 =>
      by_cases hg : t < np ∧ t ∉ l0
      · have e : (qstep np (.enQ t) (some l0)).1 = some (t :: l0) := by simp only [qstep, if_pos hg]
        rw [e]
        have hR : RepQ np l0 b := hM
        have hl0 : l0 = [] := nil_of_headD hnp' hR.2.1 (by rw [← hR.2.2.2.1]; exact hte)
        subst hl0
        have h2 : ((cE 2 "pi").eval σ1).toNat = 2 + 2 * t := cE_eval hpi1 (by omega)
        have h3 : ((cE 3 "pi").eval σ1).toNat = 3 + 2 * t := cE_eval hpi1 (by omega)
        rw [h2, h3]
        refine ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, by simp [hg.1], ?_, ?_, fun x p nx hm => ?_⟩
        · show _ = (v t)
          rw [sc_ne' (by omega), sc_eq']
        · show _ = (v t)
          rw [sc_eq']
        · simp only [links, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
          obtain ⟨rfl, rfl, rfl⟩ := hm
          refine ⟨?_, ?_⟩
          · rw [sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), sc_eq']
          · rw [sc_ne' (by omega), sc_ne' (by omega), sc_eq']
      · have e : (qstep np (.enQ t) (some l0)).1 = none := by simp only [qstep, if_neg hg]
        rw [e]; trivial
  · -- behind the tail
    have hc : (Expr.bin .eq (.var "tl") (.const (v np))).eval σ1 = 0 := by
      simp [Expr.eval, BinOp.eval, htl1, hte]
    obtain ⟨l2, w1, c2⟩ := wr_step (εR := εR) hcs hlk1 (cE 3 "tl") (.var "pi") (j := ((cE 3 "tl").eval σ1).toNat)
      rfl hpi1
    obtain ⟨l3, w2, c3⟩ := wr_step (εR := εR) c2 hlkτ1 (cE 2 "pi") (.var "tl")
      (j := ((cE 2 "pi").eval σ1).toNat) (by simp [cE, Expr.eval, L1 "pi" (by decide)])
      (show τ1 "tl" = b 1 by rw [L1 _ (by decide)]; exact htl1)
    obtain ⟨l4, w3, c4⟩ := wr_step (εR := εR) c3 hlkτ2 (cE 3 "pi") (.const (v np))
      (j := ((cE 3 "pi").eval σ1).toNat) (w := (v np)) (by simp [cE, Expr.eval, L2 "pi" (by decide)]) rfl
    obtain ⟨l5, w4, c5⟩ := wr_step (εR := εR) c4 hlkτ3 (.const (v 1)) (.var "pi") (j := 1) rfl
      (show τ3 "pi" = (v t) by rw [L3 _ (by decide)]; exact hpi1)
    refine ⟨τ4, l5, _, (qstep np (.enQ t) d).1,
      Runs.seq r0 (Runs.seq r1 (Runs.ite_false hc (Runs.seq w1 (Runs.seq w2 (Runs.seq w3 w4))))), c5, ?_, hlk4,
      fun k hk => absurd trivial hk, rfl, hR0⟩
    cases d with
    | none => trivial
    | some l0 =>
      by_cases hg : t < np ∧ t ∉ l0
      · have e : (qstep np (.enQ t) (some l0)).1 = some (t :: l0) := by simp only [qstep, if_pos hg]
        rw [e]
        have hR : RepQ np l0 b := hM
        obtain ⟨hnd, hlt, hb0, hb1, hlinks⟩ := hR
        cases l0 with
        | nil => exact absurd hb1 (by simpa using hte)
        | cons u r =>
          have hu : u < np := hlt u List.mem_cons_self
          have htl : σ1 "tl" = (v u) := by rw [htl1, hb1]; rfl
          have h3u : ((cE 3 "tl").eval σ1).toNat = 3 + 2 * u := cE_eval htl (by omega)
          have h2 : ((cE 2 "pi").eval σ1).toNat = 2 + 2 * t := cE_eval hpi1 (by omega)
          have h3 : ((cE 3 "pi").eval σ1).toNat = 3 + 2 * t := cE_eval hpi1 (by omega)
          rw [h3u, h2, h3, hb1]
          have htu : t ≠ u := fun e => hg.2 (e ▸ List.mem_cons_self)
          have htr : t ∉ r := fun h => hg.2 (List.mem_cons_of_mem _ h)
          have hur : u ∉ r := (List.nodup_cons.1 hnd).1
          refine ⟨List.nodup_cons.2 ⟨hg.2, hnd⟩, ?_, ?_, ?_, fun x p nx hm => ?_⟩
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hg.1
            · exact hlt x hx
          · show _ = (v ((t :: u :: r).getLastD np))
            rw [sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), hb0]
            simp only [List.getLastD_cons]
          · show _ = (v t)
            rw [sc_eq']
          · simp only [links, List.mem_cons, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | hm
            · refine ⟨?_, ?_⟩
              · rw [sc_ne' (by omega), sc_ne' (by omega), sc_eq']; rfl
              · rw [sc_ne' (by omega), sc_eq']
            · obtain ⟨e1, e2⟩ := hlinks x (r.headD np) np (by simp [links])
              refine ⟨?_, ?_⟩
              · rw [sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), e1]
              · rw [sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), sc_eq']
            · have hx : x ∈ r := links_mem hm
              have hxt : x ≠ t := fun e => htr (e ▸ hx)
              have hxu : x ≠ u := fun e => hur (e ▸ hx)
              obtain ⟨e1, e2⟩ := hlinks x p nx (by simp only [links]; exact List.mem_cons_of_mem _ hm)
              refine ⟨?_, ?_⟩
              · rw [sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), e1]
              · rw [sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), sc_ne' (by omega), e2]
      · have e : (qstep np (.enQ t) (some l0)).1 = none := by simp only [qstep, if_neg hg]
        rw [e]; trivial

/-! ## `deQ` -/

/-- **`dequeue` implements `deQ`.** -/
theorem deQ_impl (εR : REnv) (c : CPU) (i : Nat) {np : Nat} (hnp : 2 * np + 4 < 2 ^ 32) :
    Impl εR c i (Q np) (fun _ => True) (fun _ => True) .deQ "r" (deQS np) := by
  intro σ l b d hlk hcs hM _
  have hnp' : np < 2 ^ 32 := by omega
  let σ0 := σ.set "r" (v np)
  have r0 : Runs (rprimsA εR c) (.assign "r" (.const (v np))) σ l σ0 l := Runs.assign _ _
  have hlk0 : (σ0 "lk").toNat = i := by simpa [σ0, Locals.set] using hlk
  have r1 := rd_step (εR := εR) hcs hlk0 "hd" (.const (v 0)) (j := 0) rfl
  let σ1 := σ0.set "hd" (b 0)
  have hlk1 : (σ1 "lk").toNat = i := by simpa [σ1, σ0, Locals.set] using hlk
  have hhd1 : σ1 "hd" = b 0 := by simp [σ1, Locals.set]
  have hr1 : σ1 "r" = (v np) := by simp [σ1, σ0, Locals.set]
  have hlkσ1 : σ1 "lk" = σ "lk" := by simp [σ1, σ0, Locals.set]
  by_cases hhe : b 0 = (v np)
  · -- the queue is empty
    have hc : (Expr.bin .ne (.var "hd") (.const (v np))).eval σ1 = 0 := by
      simp [Expr.eval, BinOp.eval, hhd1, hhe]
    refine ⟨σ1, l, b, (qstep np .deQ d).1, Runs.seq r0 (Runs.seq r1 (Runs.ite_false hc Runs.skip)), hcs, ?_,
      hlkσ1, fun k hk => absurd trivial hk, rfl, ?_⟩
    · cases d with
      | none => trivial
      | some l0 =>
        have hR : RepQ np l0 b := hM
        have hl0 : l0 = [] := nil_of_getLastD hnp' hR.2.1 (by rw [← hR.2.2.1]; exact hhe)
        subst hl0; exact hR
    · intro r hr
      cases d with
      | none => simp [Q, qstep] at hr
      | some l0 =>
        have hR : RepQ np l0 b := hM
        have hl0 : l0 = [] := nil_of_getLastD hnp' hR.2.1 (by rw [← hR.2.2.1]; exact hhe)
        subst hl0
        simp only [Q, qstep, Option.some.injEq] at hr; subst hr; exact hr1
  · -- a head
    have hc : ¬ (Expr.bin .ne (.var "hd") (.const (v np))).eval σ1 = 0 := by
      simp [Expr.eval, BinOp.eval, hhd1, hhe]
    let σ2 := σ1.set "r" (σ1 "hd")
    have r2 : Runs (rprimsA εR c) (.assign "r" (.var "hd")) σ1 l σ2 l := Runs.assign _ _
    have hlk2 : (σ2 "lk").toNat = i := by simpa [σ2, σ1, σ0, Locals.set] using hlk
    let J := ((cE 3 "hd").eval σ2).toNat
    have r3 := rd_step (εR := εR) hcs hlk2 "nx" (cE 3 "hd") (j := J) rfl
    let σ3 := σ2.set "nx" (b J)
    have hnx3 : σ3 "nx" = b J := by simp [σ3, Locals.set]
    have hr3 : σ3 "r" = b 0 := by simp [σ3, σ2, Locals.set, hhd1]
    have hlk3 : (σ3 "lk").toNat = i := by simpa [σ3, σ2, σ1, σ0, Locals.set] using hlk
    have hlkσ3 : σ3 "lk" = σ "lk" := by simp [σ3, σ2, σ1, σ0, Locals.set]
    have hhd3 : σ3 "hd" = b 0 := by simp [σ3, σ2, Locals.set, hhd1]
    let τ1 := σ3.set "_" 0
    let τ2 := τ1.set "_" 0
    have L1 : ∀ z, z ≠ "_" → τ1 z = σ3 z := fun z hz => Locals.set_other _ _ hz
    have L2 : ∀ z, z ≠ "_" → τ2 z = σ3 z := fun z hz => (Locals.set_other _ _ hz).trans (L1 z hz)
    have hlkτ1 : (τ1 "lk").toNat = i := by rw [L1 _ (by decide)]; exact hlk3
    have hlk4 : τ2 "lk" = σ "lk" := by rw [L2 _ (by decide)]; exact hlkσ3
    have hr4 : τ2 "r" = b 0 := by rw [L2 _ (by decide)]; exact hr3
    -- the shape of the queue, when it is a list
    have shape : ∀ l0, RepQ np l0 b → ∃ r h, l0 = r ++ [h] ∧ h < np ∧ b 0 = (v h) ∧ J = 3 + 2 * h ∧
        b J = (v (r.getLastD np)) := by
      intro l0 hR
      obtain ⟨hnd, hlt, hb0, hb1, hlinks⟩ := hR
      rcases List.eq_nil_or_concat l0 with h0 | ⟨r, h, rfl⟩
      · subst h0; exact absurd hb0 (by simpa using hhe)
      · rw [List.concat_eq_append] at hnd hlt hb0 hlinks ⊢
        rw [getLastD_append] at hb0
        have hh : h < np := hlt h (by simp)
        have hJ : J = 3 + 2 * h := cE_eval (show σ2 "hd" = (v h) by simp [σ2, Locals.set, hhd1, hb0]) (by omega)
        refine ⟨r, h, rfl, hh, hb0, hJ, ?_⟩
        rw [hJ]
        exact (hlinks h np (r.getLastD np) (by rw [links_snoc]; simp)).2
    have hres : ∀ r, (qstep np .deQ d).2 = some r → τ2 "r" = (v r) := by
      intro r hr
      cases d with
      | none => simp [qstep] at hr
      | some l0 =>
        obtain ⟨r', h, rfl, hh, hb0, -, -⟩ := shape l0 hM
        simp only [qstep, Option.some.injEq, getLastD_append] at hr; subst hr
        rw [hr4, hb0]; rfl
    by_cases hne : b J = (v np)
    · -- the last one
      have hc2 : ¬ (Expr.bin .eq (.var "nx") (.const (v np))).eval σ3 = 0 := by
        simp [Expr.eval, BinOp.eval, hnx3, hne]
      obtain ⟨l4, w1, c4⟩ := wr_step (εR := εR) hcs hlk3 (.const (v 0)) (.const (v np)) (j := 0) (w := (v np))
        rfl rfl
      obtain ⟨l5, w2, c5⟩ := wr_step (εR := εR) c4 hlkτ1 (.const (v 1)) (.const (v np)) (j := 1) (w := (v np))
        rfl rfl
      refine ⟨τ2, l5, _, (qstep np .deQ d).1,
        Runs.seq r0 (Runs.seq r1 (Runs.ite_true hc (Runs.seq r2 (Runs.seq r3 (Runs.ite_true hc2
          (Runs.seq w1 w2)))))), c5, ?_, hlk4, fun k hk => absurd trivial hk, rfl, hres⟩
      cases d with
      | none => trivial
      | some l0 =>
        have hR : RepQ np l0 b := hM
        obtain ⟨r', h, rfl, hh, hb0, hJ, hbJ⟩ := shape _ hR
        have hr' : r' = [] := nil_of_getLastD hnp' (fun x hx => hR.2.1 x (by simp [hx]))
          (by rw [← hbJ]; exact hne)
        subst hr'
        show RepQ np ([] ++ [h]).dropLast _
        simp only [List.nil_append, List.dropLast_singleton]
        refine ⟨List.nodup_nil, fun x hx => by simp at hx, ?_, ?_, fun x p nx hm => by simp [links] at hm⟩
        · show _ = (v np); rw [sc_ne' (by omega), sc_eq']
        · show _ = (v np); rw [sc_eq']
    · -- the next one becomes the head
      have hc2 : (Expr.bin .eq (.var "nx") (.const (v np))).eval σ3 = 0 := by
        simp [Expr.eval, BinOp.eval, hnx3, hne]
      obtain ⟨l4, w1, c4⟩ := wr_step (εR := εR) hcs hlk3 (cE 2 "nx") (.const (v np))
        (j := ((cE 2 "nx").eval σ3).toNat) (w := (v np)) rfl rfl
      obtain ⟨l5, w2, c5⟩ := wr_step (εR := εR) c4 hlkτ1 (.const (v 0)) (.var "nx") (j := 0) (w := b J) rfl
        (show τ1 "nx" = b J by rw [L1 _ (by decide)]; exact hnx3)
      refine ⟨τ2, l5, _, (qstep np .deQ d).1,
        Runs.seq r0 (Runs.seq r1 (Runs.ite_true hc (Runs.seq r2 (Runs.seq r3 (Runs.ite_false hc2
          (Runs.seq w1 w2)))))), c5, ?_, hlk4, fun k hk => absurd trivial hk, rfl, hres⟩
      cases d with
      | none => trivial
      | some l0 =>
        have hR : RepQ np l0 b := hM
        obtain ⟨r, h, rfl, hh, hb0, hJ, hbJ⟩ := shape _ hR
        obtain ⟨hnd, hlt, -, hb1, hlinks⟩ := hR
        rcases List.eq_nil_or_concat r with h0 | ⟨r', n, rfl⟩
        · subst h0; exact absurd hbJ (by simpa using hne)
        · rw [List.concat_eq_append] at hnd hlt hb1 hlinks hbJ ⊢
          rw [getLastD_append] at hbJ
          have hn : n < np := hlt n (by simp)
          have hI : ((cE 2 "nx").eval σ3).toNat = 2 + 2 * n := cE_eval (by rw [hnx3, hbJ]; rfl) (by omega)
          rw [hI, hbJ]
          have hnd' : (r' ++ [n]).Nodup := (List.nodup_append.1 hnd).1
          have hnr' : n ∉ r' := by
            intro hm
            have := (List.nodup_append.1 hnd').2.2 n hm n (by simp)
            exact this rfl
          show RepQ np ((r' ++ [n]) ++ [h]).dropLast _
          rw [List.dropLast_concat]
          refine ⟨hnd', fun x hx => hlt x (List.mem_append_left _ hx), ?_, ?_, fun x p nx hm => ?_⟩
          · show _ = (v ((r' ++ [n]).getLastD np))
            rw [sc_eq', getLastD_append]
          · show _ = (v ((r' ++ [n]).headD np))
            rw [sc_ne' (by omega), sc_ne' (by omega), hb1, headD_append, headD_append, headD_append]; rfl
          · rw [links_snoc] at hm
            have hold := hlinks
            rw [links_snoc, links_snoc] at hold
            rcases List.mem_append.1 hm with hm | hm
            · have hx : x ∈ r' := links_mem hm
              have hxn : x ≠ n := fun e => hnr' (e ▸ hx)
              obtain ⟨e1, e2⟩ := hold x p nx (by simp [hm])
              refine ⟨?_, ?_⟩
              · rw [sc_ne' (by omega), sc_ne' (by omega), e1]
              · rw [sc_ne' (by omega), sc_ne' (by omega), e2]
            · simp only [List.mem_singleton, Prod.mk.injEq] at hm
              obtain ⟨hx1, hp1, hn1⟩ := hm
              subst hx1
              rw [hp1, hn1]
              obtain ⟨-, e2⟩ := hold x h (r'.getLastD np) (by simp)
              refine ⟨?_, ?_⟩
              · rw [sc_ne' (by omega), sc_eq']
              · rw [sc_ne' (by omega), sc_ne' (by omega), e2]

/-! ## Each locked call is one event -/

section Atomic
variable {εR : REnv} {ε : AEnv} {c : CPU} {l : RLog} {S : RState} {H : HLogR} {iv : Val} {np : Nat}

/-- **`acquire; enqueue(t); release` is one event `(c, enQ t)` of the queue.** -/
theorem enQ_atomic (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU) (hRA : LockArray.RelyA ε c)
    (hl : rreplay l = some (S, H)) (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hnp : 2 * np + 4 < 2 ^ 32) (t : Nat) (σ : Locals) (hσ : σ "lk" = iv) (hpi : σ "pi" = (v t))
    (hRJ : RelyJ εR c iv.toNat (Q np).J) (hJ : (Q np).J (hmemR iv.toNat H)) :
    ∃ H1 : HLogR, (Q np).J (hmemR iv.toNat H1) ∧
      ∀ h, (Q np).rep ((Q np).replay h) (hmemR iv.toNat H1) →
        ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq (enQS np) relA), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          (Q np).rep ((Q np).replay ((c, .enQ t) :: h)) (hmemR iv.toNat H3) ∧ (Q np).J (hmemR iv.toNat H3) ∧
          ∀ r, (Q np).result h c (.enQ t) = some r → σ' "r" = (v r) :=
  atomic_call hE hRR hc hRA hl hidle bound K hK hF σ hσ (enQ_impl εR c iv.toNat hnp t) (by decide)
    (fun σ1 hfr => by rw [hfr "pi" (by decide) (by decide) (by decide) (by decide)]; exact hpi) hRJ hJ

/-- **`acquire; dequeue(); release` is one event `(c, deQ)` of the queue**:
the thread it returns is the head of the queue after the history it found. -/
theorem deQ_atomic (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU) (hRA : LockArray.RelyA ε c)
    (hl : rreplay l = some (S, H)) (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hnp : 2 * np + 4 < 2 ^ 32) (σ : Locals) (hσ : σ "lk" = iv)
    (hRJ : RelyJ εR c iv.toNat (Q np).J) (hJ : (Q np).J (hmemR iv.toNat H)) :
    ∃ H1 : HLogR, (Q np).J (hmemR iv.toNat H1) ∧
      ∀ h, (Q np).rep ((Q np).replay h) (hmemR iv.toNat H1) →
        ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq (deQS np) relA), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          (Q np).rep ((Q np).replay ((c, .deQ) :: h)) (hmemR iv.toNat H3) ∧ (Q np).J (hmemR iv.toNat H3) ∧
          ∀ r, (Q np).result h c .deQ = some r → σ' "r" = (v r) :=
  atomic_call hE hRR hc hRA hl hidle bound K hK hF σ hσ (deQ_impl εR c iv.toNat hnp) (by decide)
    (fun _ _ => trivial) hRJ hJ

end Atomic

end MC2Queue
