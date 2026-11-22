import CertiKOS.MC2Queue

/-!
# mC2: the scheduling layer `L_btd[c]`

The scheduling layer of mC2 ([PLDI18] §5.1, [OSDI16] Fig. 3 and Fig. 9).
Every thread belongs to one CPU (`own`, fixed at creation). Each CPU has a
private ready queue and a current thread; the pending queue of each CPU and
the sleeping queues are shared queues (`MC2Queue`), each an atomic object on
its own lock.

* `yield`: move the head of this CPU's pending queue to its ready queue, put
  the running thread at the tail of the ready queue, and switch to the head.
* `sleep(i, lk)`: put the running thread on sleeping queue `i` and switch to
  the head of the ready queue.
* `wakeup(i)`: take the head of sleeping queue `i`. If it belongs to this CPU
  it goes to the ready queue; otherwise to its CPU's pending queue.

**The machine.** Each operation is a few steps (`SOp`), and every step is
either one event of a shared queue (`c.enQ`, `c.deQ` on `QId`) or private to
the CPU, so the steps of different CPUs interleave arbitrarily: this is the
hardware scheduler. A CPU's program counter (`PC`) says which step comes
next.

| operation | steps |
|---|---|
| `yield` | `yield1`: `deQ` on `PendQ c`, the thread to the ready queue; `yield2`: the running thread to the ready queue; `pick` |
| `sleep(i, lk)` | `sleep1 i`: `enQ` the running thread on `SleepQ i`; `pick` |
| `wakeup(i)` | `wake1 i`: `deQ` on `SleepQ i`, to the ready queue if the thread is ours; `wake2`: else `enQ` on its CPU's `PendQ` |

`pick` is `cswitch`: the head of the ready queue becomes the running thread
(none if the queue is empty; the CPU then idles, calling `yield`).

* `St`: the shared log of queue events and each CPU's private state. The
  state of a shared queue is the **replay** of its events (`qs`, through
  `MC2Queue.Q`), and a dequeue's result is the object's `result`: exactly what
  `deQ_atomic` and `enQ_atomic` guarantee for the locked calls.
* `replayS`: the state after a log of steps; `Rsched L c` is the thread
  running on CPU `c` after the log `L` ([PLDI18]'s `R_sched`).
* `Wf`: **every thread is in exactly one place**: running on its CPU, on its
  CPU's ready or pending queue, on a sleeping queue, or held by a CPU between
  the two halves of a `wakeup`. No queue holds a thread twice, and every
  shared queue is defined.
* `wf_replay`: every reachable state is `Wf`. So no queue is ever
  enqueued a thread already on it (`queues_defined`): the obligation stage 2
  left. A running thread runs on its own CPU only and is on no queue
  (`running_alone`).

**Decisions of ours.** The papers give no code for these operations. The
step split, the order of `yield`'s two moves (as in mCertiKOS's
`thread_yield`), and the idle CPU are ours. The release of `lk` in
`sleep(i, lk)` belongs to the synchronisation layer (stage 5); here it is
after `sleep1`, which is what prevents lost wakeups. The ready queue and the
running thread are kept abstract here; their code, on per-CPU memory, and
`cswitch`'s saved registers come with the thread layers.
-/

set_option linter.unusedVariables false

namespace MC2Sched

open MC2 MC2Queue

/-! ## The state -/

/-- A shared queue: a CPU's pending queue, or a sleeping queue. -/
inductive QId
  | pend (c : Nat)
  | sleep (i : Nat)
  deriving DecidableEq

/-- The next step of a CPU's current operation. -/
inductive PC
  | idle
  | y2
  | pk
  | w2 (t : Nat)
  deriving DecidableEq

/-- A CPU's private state: its ready queue (tail first, as `PAbQueue`), its
running thread, and where it is in an operation. -/
structure Priv where
  rdq : List Nat
  cur : Option Nat
  pc : PC

/-- The shared log of queue events (newest first) and the private states. -/
structure St where
  ql : List (QId × Nat × QOp)
  pv : Nat → Priv

def upd {α : Type} (f : Nat → α) (a : Nat) (b : α) : Nat → α := fun x => if x = a then b else f x

@[simp] theorem upd_self {α : Type} (f : Nat → α) (a : Nat) (b : α) : upd f a b a = b := by simp [upd]
theorem upd_cur (f : Nat → Priv) (a x : Nat) (b : Priv) : (upd f a b x).cur = if x = a then b.cur else (f x).cur := by
  unfold upd; split <;> rfl
theorem upd_rdq (f : Nat → Priv) (a x : Nat) (b : Priv) : (upd f a b x).rdq = if x = a then b.rdq else (f x).rdq := by
  unfold upd; split <;> rfl
theorem upd_pc (f : Nat → Priv) (a x : Nat) (b : Priv) : (upd f a b x).pc = if x = a then b.pc else (f x).pc := by
  unfold upd; split <;> rfl
theorem upd_ne {α : Type} (f : Nat → α) {a x : Nat} (b : α) (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

/-- The events of queue `q`. -/
def proj (q : QId) : List (QId × Nat × QOp) → List (Nat × QOp)
  | [] => []
  | (q', c, o) :: l => if q' = q then (c, o) :: proj q l else proj q l

variable (np : Nat) (own : Nat → Nat)

/-- The replay of a queue's events: `(Q np).replay` (`qrep_eq`). -/
def qrep : List (Nat × QOp) → Option (List Nat)
  | [] => some []
  | (_, o) :: h => (qstep np o (qrep h)).1

theorem qrep_eq (h : List (Nat × QOp)) : qrep np h = (Q np).replay h := by
  induction h with
  | nil => rfl
  | cons e h ih => obtain ⟨c, o⟩ := e; simp only [qrep, ih]; rfl

/-- **The state of a shared queue is the replay of its events.** -/
def qs (ql : List (QId × Nat × QOp)) (q : QId) : Option (List Nat) := qrep np (proj q ql)

/-- What a dequeue on `q` returns after `ql` (`np` when unspecified). -/
def qres (ql : List (QId × Nat × QOp)) (q : QId) : Nat := ((qstep np .deQ (qs np ql q)).2).getD np

/-- `qres` is the queue object's result. -/
theorem qres_result (ql : List (QId × Nat × QOp)) (q : QId) (c : Nat) :
    qres np ql q = ((Q np).result (proj q ql) c .deQ).getD np := by
  unfold qres qs AObj.result; rw [qrep_eq]; rfl

/-! ## The steps -/

inductive SOp
  | yield1
  | yield2
  | sleep1 (i : Nat)
  | pick
  | wake1 (i : Nat)
  | wake2

/-- `cswitch`: the head of the ready queue runs. -/
def pickP (p : Priv) : Priv :=
  if p.rdq = [] then { p with pc := .idle } else ⟨p.rdq.dropLast, some (p.rdq.getLastD np), .idle⟩

/-- **One step of CPU `c`**, or `none` if the step is not the CPU's next. -/
def stepE (s : St) (c : Nat) : SOp → Option St
  | .yield1 =>
    if (s.pv c).pc = .idle then
      let r := qres np s.ql (.pend c)
      some ⟨(.pend c, c, .deQ) :: s.ql,
        upd s.pv c { s.pv c with rdq := if r = np then (s.pv c).rdq else r :: (s.pv c).rdq, pc := .y2 }⟩
    else none
  | .yield2 =>
    if (s.pv c).pc = .y2 then
      some ⟨s.ql, upd s.pv c ⟨(s.pv c).cur.toList ++ (s.pv c).rdq, none, .pk⟩⟩
    else none
  | .sleep1 i =>
    match (s.pv c).pc, (s.pv c).cur with
    | .idle, some t => some ⟨(.sleep i, c, .enQ t) :: s.ql, upd s.pv c { s.pv c with cur := none, pc := .pk }⟩
    | _, _ => none
  | .pick =>
    if (s.pv c).pc = .pk ∧ (s.pv c).cur = none then some ⟨s.ql, upd s.pv c (pickP np (s.pv c))⟩ else none
  | .wake1 i =>
    if (s.pv c).pc = .idle then
      let r := qres np s.ql (.sleep i)
      let ql' := (.sleep i, c, .deQ) :: s.ql
      some (if r = np then ⟨ql', s.pv⟩
        else if own r = c then ⟨ql', upd s.pv c { s.pv c with rdq := r :: (s.pv c).rdq }⟩
        else ⟨ql', upd s.pv c { s.pv c with pc := .w2 r }⟩)
    else none
  | .wake2 =>
    match (s.pv c).pc with
    | .w2 t => some ⟨(.pend (own t), c, .enQ t) :: s.ql, upd s.pv c { s.pv c with pc := .idle }⟩
    | _ => none

/-- At the start, every thread is on its CPU's ready queue. -/
def init : St := ⟨[], fun c => ⟨(List.range np).filter (fun t => own t = c), none, .idle⟩⟩

/-- The state after a log of steps, newest first. -/
def replayS : List (Nat × SOp) → Option St
  | [] => some (init np own)
  | (c, e) :: L => (replayS L).bind (fun s => stepE np own s c e)

/-- **`R_sched`**: the thread running on CPU `c` after the log `L`. -/
def Rsched (L : List (Nat × SOp)) (c : Nat) : Option Nat := (replayS np own L).bind (fun s => (s.pv c).cur)

/-! ## Where a thread is -/

inductive Place
  | run (c : Nat)
  | ready (c : Nat)
  | pend (c : Nat)
  | sleep (i : Nat)
  | transit (c : Nat)
  deriving DecidableEq

def trL : PC → List Nat
  | .w2 t => [t]
  | _ => []

@[simp] theorem trL_idle : trL .idle = [] := rfl
@[simp] theorem trL_y2 : trL .y2 = [] := rfl
@[simp] theorem trL_pk : trL .pk = [] := rfl
@[simp] theorem trL_w2 (t : Nat) : trL (.w2 t) = [t] := rfl

theorem trL_ite (P : Prop) [Decidable P] (a b : PC) : trL (if P then a else b) = if P then trL a else trL b := by
  split <;> rfl

/-- The threads at a place. -/
def view (s : St) : Place → List Nat
  | .run c => (s.pv c).cur.toList
  | .ready c => (s.pv c).rdq
  | .pend c => (qs np s.ql (.pend c)).getD []
  | .sleep i => (qs np s.ql (.sleep i)).getD []
  | .transit c => trL (s.pv c).pc

/-- A thread runs, is ready or pending only on its own CPU. -/
def Ok (t : Nat) : Place → Prop
  | .run c | .ready c | .pend c => own t = c
  | _ => True

/-- **Every thread is in exactly one place**, no list repeats a thread, and
every shared queue is defined. -/
def Wf (s : St) : Prop :=
  (∀ q, qs np s.ql q ≠ none) ∧ (∀ p, (view np s p).Nodup) ∧
    ∃ pl : Nat → Place, (∀ t p, t ∈ view np s p ↔ t < np ∧ pl t = p) ∧ ∀ t, t < np → Ok own t (pl t)

/-! ## Lemmas -/

theorem qs_cons (q : QId) (c : Nat) (o : QOp) (ql : List (QId × Nat × QOp)) (r : QId) :
    qs np ((q, c, o) :: ql) r = if r = q then (qstep np o (qs np ql r)).1 else qs np ql r := by
  unfold qs; by_cases h : q = r
  · subst h; simp [proj, qrep]
  · simp [proj, h, Ne.symm h]

theorem qres_eq {ql : List (QId × Nat × QOp)} {q : QId} {l : List Nat} (h : qs np ql q = some l) :
    qres np ql q = l.getLastD np := by
  unfold qres; rw [h]; rfl

theorem mem_dropLast {l : List Nat} {d x : Nat} (hn : l.Nodup) (hne : l ≠ []) :
    x ∈ l.dropLast ↔ x ∈ l ∧ x ≠ l.getLastD d := by
  rcases List.eq_nil_or_concat l with h | ⟨l', a, rfl⟩
  · exact absurd h hne
  · rw [List.concat_eq_append, PAbQueue.getLastD_append, List.dropLast_concat] at *
    have ha : a ∉ l' := by
      intro hm; rw [List.nodup_append] at hn; exact hn.2.2 a hm a (by simp) rfl
    constructor
    · intro hx; exact ⟨by simp [hx], fun e => ha (by have e' : x = a := e; rw [← e']; exact hx)⟩
    · rintro ⟨hx, hne'⟩; simp at hx; rcases hx with hx | hx
      · exact hx
      · exact absurd hx hne'

theorem getLastD_mem {l : List Nat} {d : Nat} (hne : l ≠ []) : l.getLastD d ∈ l := by
  rcases List.eq_nil_or_concat l with h | ⟨l', a, rfl⟩
  · exact absurd h hne
  · rw [List.concat_eq_append, PAbQueue.getLastD_append]; simp

variable {np own}

/-- In a `Wf` state a thread is in one place only. -/
theorem uniq {s : St} (hW : Wf np own s) {t : Nat} {p p' : Place} (h : t ∈ view np s p) (h' : t ∈ view np s p') :
    p = p' := by
  obtain ⟨-, -, pl, hpl, -⟩ := hW
  exact ((hpl t p).1 h).2.symm.trans ((hpl t p').1 h').2

theorem lt_of_mem {s : St} (hW : Wf np own s) {t : Nat} {p : Place} (h : t ∈ view np s p) : t < np := by
  obtain ⟨-, -, pl, hpl, -⟩ := hW; exact ((hpl t p).1 h).1

theorem ok_of_mem {s : St} (hW : Wf np own s) {t : Nat} {p : Place} (h : t ∈ view np s p) : Ok own t p := by
  obtain ⟨-, -, pl, hpl, hok⟩ := hW
  obtain ⟨hlt, hp⟩ := (hpl t p).1 h; rw [← hp]; exact hok t hlt

theorem qs_some {s : St} (hW : Wf np own s) (q : QId) : ∃ l, qs np s.ql q = some l := by
  cases h : qs np s.ql q with
  | none => exact absurd h (hW.1 q)
  | some l => exact ⟨l, rfl⟩

/-- A step that moves no thread keeps `Wf`. -/
theorem wf_same {s s' : St} (hW : Wf np own s) (hq : ∀ q, qs np s'.ql q ≠ none)
    (hv : ∀ p, view np s' p = view np s p) : Wf np own s' := by
  obtain ⟨-, hn, pl, hpl, hok⟩ := hW
  exact ⟨hq, fun p => hv p ▸ hn p, pl, fun t p => hv p ▸ hpl t p, hok⟩

/-- **A step that moves one thread `t` from `p1` to `p2` keeps `Wf`.** -/
theorem wf_move {s s' : St} (hW : Wf np own s) (hq : ∀ q, qs np s'.ql q ≠ none) {p1 p2 : Place} {t : Nat}
    (h12 : p1 ≠ p2) (ht : t ∈ view np s p1) (hok : Ok own t p2)
    (hsame : ∀ p, p ≠ p1 → p ≠ p2 → view np s' p = view np s p)
    (h1 : ∀ x, x ∈ view np s' p1 ↔ x ∈ view np s p1 ∧ x ≠ t) (h2 : ∀ x, x ∈ view np s' p2 ↔ x ∈ view np s p2 ∨ x = t)
    (n1 : (view np s' p1).Nodup) (n2 : (view np s' p2).Nodup) : Wf np own s' := by
  have htl := lt_of_mem hW ht
  have hu := @uniq np own s hW
  obtain ⟨-, hn, pl, hpl, hokl⟩ := hW
  have hpt : pl t = p1 := ((hpl t p1).1 ht).2
  refine ⟨hq, fun p => ?_, fun x => if x = t then p2 else pl x, fun x p => ?_, fun x hx => ?_⟩
  · by_cases e1 : p = p1
    · subst e1; exact n1
    · by_cases e2 : p = p2
      · subst e2; exact n2
      · rw [hsame p e1 e2]; exact hn p
  · by_cases e1 : p = p1
    · subst e1; rw [h1, hpl]
      by_cases ex : x = t
      · subst ex; simp [Ne.symm h12]
      · simp [ex]
    · by_cases e2 : p = p2
      · subst e2; rw [h2, hpl]
        by_cases ex : x = t
        · subst ex; simp [htl]
        · simp [ex]
      · rw [hsame p e1 e2, hpl]
        by_cases ex : x = t
        · subst ex; simp only [ite_true]
          constructor
          · rintro ⟨-, hp⟩; exact absurd (hp.symm.trans hpt) e1
          · rintro ⟨-, hp⟩; exact absurd hp.symm e2
        · simp [ex]
  · by_cases ex : x = t
    · subst ex; simp only [ite_true]; exact hok
    · simp only [ex, ite_false]; exact hokl x hx

/-! ## The invariant -/

theorem wf_init : Wf np own (init np own) := by
  refine ⟨fun q => by simp [qs, init, proj, qrep], fun p => ?_, fun t => .ready (own t),
    fun t p => ?_, fun t _ => by simp [Ok]⟩
  · cases p <;> simp [view, init, qs, proj, qrep, trL]
    exact (List.nodup_range).filter _
  · cases p <;> simp [view, init, qs, proj, qrep, trL]

theorem nodup_cons_of {s : St} (hW : Wf np own s) {t : Nat} {p p' : Place} (ht : t ∈ view np s p) (hne : p ≠ p') :
    (t :: view np s p').Nodup :=
  List.nodup_cons.2 ⟨fun h => hne (uniq hW ht h), hW.2.1 p'⟩

theorem view_q {s : St} {q : QId} {l : List Nat} (hl : qs np s.ql q = some l) :
    view np s (match q with | .pend c => .pend c | .sleep i => .sleep i) = l := by
  cases q <;> simp [view, hl]

/-- The queue `q` after enqueuing `t`, a thread on no queue, is defined. -/
theorem hq_enQ {s : St} (hW : Wf np own s) {q : QId} {l : List Nat} (hl : qs np s.ql q = some l) {t : Nat}
    (ht : t < np) (hnt : t ∉ l) (c : Nat) : ∀ r, qs np ((q, c, .enQ t) :: s.ql) r ≠ none := by
  intro r; rw [qs_cons]; split
  · next e => subst e; rw [hl]; simp [qstep, ht, hnt]
  · exact hW.1 r

theorem hq_deQ {s : St} (hW : Wf np own s) {q : QId} {l : List Nat} (hl : qs np s.ql q = some l) (c : Nat) :
    ∀ r, qs np ((q, c, .deQ) :: s.ql) r ≠ none := by
  intro r; rw [qs_cons]; split
  · next e => subst e; rw [hl]; simp [qstep]
  · exact hW.1 r

theorem wf_yield1 {s s' : St} {c : Nat} (hW : Wf np own s) (h : stepE np own s c .yield1 = some s') :
    Wf np own s' := by
  simp only [stepE] at h
  split at h
  · next hpc =>
    cases h
    obtain ⟨l, hl⟩ := qs_some hW (.pend c)
    have hvl : view np s (.pend c) = l := by simp [view, hl]
    have hq := hq_deQ hW hl c
    rw [qres_eq np hl]
    by_cases hne : l = []
    · subst hne
      simp only [List.getLastD_nil, ite_true]
      refine wf_same hW hq (fun p => ?_)
      clear hW hq
      cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
    · have hr : l.getLastD np ∈ view np s (.pend c) := by rw [hvl]; exact getLastD_mem hne
      have hlt := lt_of_mem hW hr
      have hok : own (l.getLastD np) = c := ok_of_mem hW hr
      rw [if_neg (by omega)]
      have hnod : l.Nodup := hvl ▸ hW.2.1 (.pend c)
      refine wf_move hW hq (p1 := .pend c) (p2 := .ready c) (by simp) hr hok ?_ ?_ ?_ ?_ ?_
      · intro p hp1 hp2; clear hW hq hr hnod
        cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
      · intro x; simp only [view, qs_cons, if_true, hl, qstep, Option.getD]; (try rw [hvl]); exact mem_dropLast hnod hne
      · intro x; simp [view, upd, or_comm]
      · simp only [view, qs_cons, if_true, hl, qstep, Option.getD]
        exact hnod.sublist (List.dropLast_sublist _)
      · simpa [view, upd] using nodup_cons_of hW hr (p' := .ready c) (by simp)
  · cases h

theorem wf_yield2 {s s' : St} {c : Nat} (hW : Wf np own s) (h : stepE np own s c .yield2 = some s') :
    Wf np own s' := by
  simp only [stepE] at h
  split at h
  · next hpc =>
    cases h
    cases hcur : (s.pv c).cur with
    | none =>
      refine wf_same hW hW.1 (fun p => ?_)
      clear hW
      cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
    | some t =>
      have ht : t ∈ view np s (.run c) := by simp [view, hcur]
      refine wf_move hW hW.1 (p1 := .run c) (p2 := .ready c) (by simp) ht (ok_of_mem hW ht : own _ = c) ?_ ?_ ?_ ?_ ?_
      · intro p hp1 hp2; clear hW ht
        cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
      · intro x; simp [view, upd, hcur]
      · intro x; simp [view, upd, hcur, or_comm]
      · simp [view, upd]
      · simpa [view, upd, hcur] using nodup_cons_of hW ht (p' := .ready c) (by simp)
  · cases h

theorem wf_sleep1 {s s' : St} {c i : Nat} (hW : Wf np own s) (h : stepE np own s c (.sleep1 i) = some s') :
    Wf np own s' := by
  simp only [stepE] at h
  split at h
  · next t hpc hcur =>
    cases h
    have ht : t ∈ view np s (.run c) := by simp [view, hcur]
    obtain ⟨l, hl⟩ := qs_some hW (.sleep i)
    have hvl : view np s (.sleep i) = l := by simp [view, hl]
    have hnt : t ∉ l := fun hm => by have := uniq hW ht (hvl ▸ hm); simp at this
    have hq := hq_enQ hW hl (lt_of_mem hW ht) hnt c
    refine wf_move hW hq (p1 := .run c) (p2 := .sleep i) (by simp) ht trivial ?_ ?_ ?_ ?_ ?_
    · intro p hp1 hp2; clear hW ht hq
      cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
    · intro x; simp [view, upd, hcur]
    · intro x; simp [view, qs_cons, hl, qstep, lt_of_mem hW ht, hnt, or_comm]
    · simp [view, upd]
    · simpa [view, qs_cons, hl, qstep, lt_of_mem hW ht, hnt] using nodup_cons_of hW ht (p' := .sleep i) (by simp)
  · cases h

theorem wf_pick {s s' : St} {c : Nat} (hW : Wf np own s) (h : stepE np own s c .pick = some s') :
    Wf np own s' := by
  simp only [stepE] at h
  split at h
  · next hc =>
    obtain ⟨hpc, hcur⟩ := hc
    cases h
    unfold pickP
    by_cases hne : (s.pv c).rdq = []
    · rw [if_pos hne]
      refine wf_same hW hW.1 (fun p => ?_)
      clear hW
      cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
    · rw [if_neg hne]
      have hnod : (s.pv c).rdq.Nodup := hW.2.1 (.ready c)
      have ht : (s.pv c).rdq.getLastD np ∈ view np s (.ready c) := getLastD_mem hne
      refine wf_move hW hW.1 (p1 := .ready c) (p2 := .run c) (by simp) ht (ok_of_mem hW ht : own _ = c) ?_ ?_ ?_ ?_ ?_
      · intro p hp1 hp2; clear hW ht hnod
        cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
      · intro x; simp only [view, upd_self]; exact mem_dropLast hnod hne
      · intro x; simp [view, hcur]
      · simp only [view, upd_self]; exact hnod.sublist (List.dropLast_sublist _)
      · simp [view]
  · cases h

theorem wf_wake1 {s s' : St} {c i : Nat} (hW : Wf np own s) (h : stepE np own s c (.wake1 i) = some s') :
    Wf np own s' := by
  simp only [stepE] at h
  split at h
  · next hpc =>
    cases h
    obtain ⟨l, hl⟩ := qs_some hW (.sleep i)
    have hvl : view np s (.sleep i) = l := by simp [view, hl]
    have hq := hq_deQ hW hl c
    rw [qres_eq np hl]
    by_cases hne : l = []
    · subst hne
      simp only [List.getLastD_nil, ite_true]
      refine wf_same hW hq (fun p => ?_)
      clear hW hq
      cases p <;> simp only [view, qs_cons] <;> (try split) <;> simp_all [qstep]
    · have hr : l.getLastD np ∈ view np s (.sleep i) := by rw [hvl]; exact getLastD_mem hne
      have hlt := lt_of_mem hW hr
      have hnod : l.Nodup := hvl ▸ hW.2.1 (.sleep i)
      rw [if_neg (by omega)]
      have e1 : ∀ x, x ∈ view np ⟨(.sleep i, c, .deQ) :: s.ql, s.pv⟩ (.sleep i) ↔ x ∈ view np s (.sleep i) ∧ x ≠ l.getLastD np := by
        intro x; simp only [view, qs_cons, if_true, hl, qstep, Option.getD]; (try rw [hvl]); exact mem_dropLast hnod hne
      have n1 : (view np ⟨(.sleep i, c, .deQ) :: s.ql, s.pv⟩ (.sleep i)).Nodup := by
        simp only [view, qs_cons, if_true, hl, qstep, Option.getD]; exact hnod.sublist (List.dropLast_sublist _)
      by_cases ho : own (l.getLastD np) = c
      · rw [if_pos ho]
        refine wf_move hW hq (p1 := .sleep i) (p2 := .ready c) (by simp) hr ho ?_ e1 ?_ n1 ?_
        · intro p hp1 hp2; clear hW hq hr hnod e1 n1
          cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
        · intro x; simp [view, upd, or_comm]
        · simpa [view, upd] using nodup_cons_of hW hr (p' := .ready c) (by simp)
      · rw [if_neg ho]
        refine wf_move hW hq (p1 := .sleep i) (p2 := .transit c) (by simp) hr trivial ?_ e1 ?_ n1 ?_
        · intro p hp1 hp2; clear hW hq hr hnod e1 n1
          cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
        · intro x; simp [view, upd, trL, hpc]
        · simp [view, upd, trL]
  · cases h

theorem wf_wake2 {s s' : St} {c : Nat} (hW : Wf np own s) (h : stepE np own s c .wake2 = some s') :
    Wf np own s' := by
  simp only [stepE] at h
  split at h
  · next t hpc =>
    cases h
    have ht : t ∈ view np s (.transit c) := by simp [view, hpc, trL]
    obtain ⟨l, hl⟩ := qs_some hW (.pend (own t))
    have hvl : view np s (.pend (own t)) = l := by simp [view, hl]
    have hnt : t ∉ l := fun hm => by have := uniq hW ht (hvl ▸ hm); simp at this
    have hlt := lt_of_mem hW ht
    have hq := hq_enQ hW hl hlt hnt c
    refine wf_move hW hq (p1 := .transit c) (p2 := .pend (own t)) (by simp) ht rfl ?_ ?_ ?_ ?_ ?_
    · intro p hp1 hp2; clear hW ht hq
      cases p <;> rename_i c' <;> by_cases e : c' = c <;> first | (subst e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep]) | (have e' : c ≠ c' := Ne.symm e; simp_all [view, upd_cur, upd_rdq, upd_pc, trL_ite, qs_cons, qstep])
    · intro x; simp [view, upd, hpc, trL]
    · intro x; simp [view, qs_cons, hl, qstep, hlt, hnt, or_comm]
    · simp [view, upd, trL]
    · simpa [view, qs_cons, hl, qstep, hlt, hnt] using nodup_cons_of hW ht (p' := .pend (own t)) (by simp)
  · cases h

/-- **Every step keeps the invariant.** -/
theorem wf_step {s s' : St} {c : Nat} {e : SOp} (hW : Wf np own s) (h : stepE np own s c e = some s') :
    Wf np own s' := by
  cases e with
  | yield1 => exact wf_yield1 hW h
  | yield2 => exact wf_yield2 hW h
  | sleep1 i => exact wf_sleep1 hW h
  | pick => exact wf_pick hW h
  | wake1 i => exact wf_wake1 hW h
  | wake2 => exact wf_wake2 hW h

/-- **Every reachable state is `Wf`**, for any interleaving of the CPUs' steps. -/
theorem wf_replay {L : List (Nat × SOp)} {s : St} (h : replayS np own L = some s) : Wf np own s := by
  induction L generalizing s with
  | nil => simp [replayS] at h; subst h; exact wf_init
  | cons e L ih =>
    obtain ⟨c, e⟩ := e
    simp only [replayS] at h
    cases hL : replayS np own L with
    | none => rw [hL] at h; cases h
    | some s0 => rw [hL] at h; exact wf_step (ih hL) h

/-- **No shared queue is ever enqueued a thread already on it**: every queue
stays defined, which is the obligation `MC2Queue` left (its state is `none`
from the first bad `enQ` on). -/
theorem queues_defined {L : List (Nat × SOp)} {s : St} (h : replayS np own L = some s) (q : QId) :
    qs np s.ql q ≠ none :=
  (wf_replay h).1 q

/-- **A running thread runs on its own CPU only, and is on no queue.** -/
theorem running_alone {L : List (Nat × SOp)} {s : St} (h : replayS np own L = some s) {c t : Nat}
    (hc : (s.pv c).cur = some t) :
    own t = c ∧ t < np ∧ ∀ p, t ∈ view np s p → p = .run c := by
  have hW := wf_replay h
  have ht : t ∈ view np s (.run c) := by simp [view, hc]
  exact ⟨ok_of_mem hW ht, lt_of_mem hW ht, fun p hp => uniq hW hp ht⟩

/-- `R_sched` in these terms: the thread it gives runs on its own CPU and on no
other. -/
theorem rsched_owner {L : List (Nat × SOp)} {c t : Nat} (h : Rsched np own L c = some t) :
    own t = c ∧ t < np ∧ ∀ c', Rsched np own L c' = some t → c' = c := by
  unfold Rsched at h ⊢
  cases hL : replayS np own L with
  | none => rw [hL] at h; cases h
  | some s =>
    rw [hL] at h; simp only [Option.bind] at h
    obtain ⟨ho, hlt, hu⟩ := running_alone hL h
    refine ⟨ho, hlt, fun c' hc' => ?_⟩
    simp only [Option.bind] at hc'
    have := hu (.run c') (by simp [view, hc'])
    simpa using this

end MC2Sched
