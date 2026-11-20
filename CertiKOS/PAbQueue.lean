import CertiKOS.PQueueInit

/-!
# mCertiKOS `PAbQueue`: queues as lists, ported

The layer above `PQueueInit` forgets the pointers. A queue is a list of
thread ids, and a thread records which queue it is on.

Ported from `layerlib/AuxStateDataType.v`: `AbQueue`, `AbTCB`, and the
invariants `AbTCBCorrect_range`, `AbQCorrect_range`, `NotInQ`, `QCount`,
`InQ`.

Ported from `objects/ObjThread.v`: `get_state0_spec`, `set_state0_spec`,
`enqueue0_spec`, `dequeue0_spec`, `queue_rmv0_spec`, `tdqueue_init0_spec`.
Ported from `clib/CalRealProcModule.v`: `real_abtcb`, `real_abq`.

Ported from `proc/AbQueueGen.v`: the relation between the two views,
`abqueue_match_next_prev_rec`, `abqueue_match_dllist`, `abtcbpool_tcbpool`,
`AbQ_RealQ`, and the theorems that each list operation is matched by the
pointer operation: `real_data`, `get_state_exists`, `set_state_exists`,
`enqueue_exists`, `dequeue_exists`, `queue_rmv_exists`.

The proofs are new. mCertiKOS reasons on the recursive relation directly.
Here `rec_iff` restates it: a list `l` (tail first) matches when the head is
its last element, the tail its first, and every `(x, prev, next)` in
`links l` is the control block of `x`. Appending lists appends their links
(`links_append`), which gives the four ways a thread leaves a queue.

What differs: the queue a thread is on is an `Int`, `-1` for none, as in
mCertiKOS. Coq's `remove` is `remove` here (a filter).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PAbQueue

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue

/-! ## Abstract data (`AuxStateDataType.v`) -/

/-- `AbQValid l`: the threads on the queue, the tail first. -/
inductive AbQueue
  | AbQUndef
  | AbQValid (l : List Nat)

abbrev AbQueuePool := Nat → AbQueue

/-- `AbTCBValid state inQ`: `inQ` is the queue the thread is on, `-1` for none. -/
inductive AbTCB
  | AbTCBUndef
  | AbTCBValid (tds : ThreadState) (inQ : Int)

abbrev AbTCBPool := Nat → AbTCB

/-- `SData` with the abstract threads and queues. -/
structure AData extends SData where
  abtcb : AbTCBPool
  abq : AbQueuePool

/-- Coq's `remove`: every occurrence of `x`. -/
def remove (x : Nat) (l : List Nat) : List Nat := l.filter (fun y => y != x)

/-! ## Specifications (`ObjThread.v`) -/

section Specs
variable (num_proc num_chan : Nat)

def get_state0_spec (n : Nat) (d : AData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    match d.abtcb n with
    | .AbTCBValid s _ => some (ThreadStatetoZ s)
    | .AbTCBUndef => none
  else none

/-- `set_state0_spec`. The bound is `num_id` in mCertiKOS, the same constant
as `num_proc`. -/
def set_state0_spec (num_id n s : Nat) (d : AData) : Option AData :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_id then
    if (d.AC n).cused = true then
      match d.abtcb n, ZtoThreadState s with
      | .AbTCBValid _ b, some i => some { d with abtcb := setAt d.abtcb n (.AbTCBValid i b) }
      | _, _ => none
    else none
  else none

/-- **`enqueue0_spec`**: a thread on no queue goes to the front of the list. -/
def enqueue0_spec (n i : Nat) (d : AData) : Option AData :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc then
    match d.abq n with
    | .AbQUndef => none
    | .AbQValid l =>
      if (d.AC i).cused = true then
        match d.abtcb i with
        | .AbTCBUndef => none
        | .AbTCBValid st b =>
          if b = -1 then
            some { d with
              abtcb := setAt d.abtcb i (.AbTCBValid st n)
              abq := setAt d.abq n (.AbQValid (i :: l)) }
          else none
      else none
  else none

/-- **`dequeue0_spec`**: the last of the list leaves. -/
def dequeue0_spec (n : Nat) (d : AData) : Option (AData × Nat) :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan then
    match d.abq n with
    | .AbQUndef => none
    | .AbQValid l =>
      if l.getLastD num_proc = num_proc then some (d, l.getLastD num_proc)
      else
        match d.abtcb (l.getLastD num_proc) with
        | .AbTCBUndef => none
        | .AbTCBValid st _ =>
          some ({ d with
            abtcb := setAt d.abtcb (l.getLastD num_proc) (.AbTCBValid st (-1))
            abq := setAt d.abq n (.AbQValid (remove (l.getLastD num_proc) l)) }, l.getLastD num_proc)
  else none

/-- **`queue_rmv0_spec`**: thread `i`, which is on queue `n`, leaves it. -/
def queue_rmv0_spec (n i : Nat) (d : AData) : Option AData :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan ∧ i < num_proc then
    match d.abq n with
    | .AbQUndef => none
    | .AbQValid l =>
      match d.abtcb i with
      | .AbTCBUndef => none
      | .AbTCBValid st b =>
        if (n : Int) = b then
          some { d with
            abtcb := setAt d.abtcb i (.AbTCBValid st (-1))
            abq := setAt d.abq n (.AbQValid (remove i l)) }
        else none
  else none

end Specs

/-- `real_abtcb`: every thread dead and on no queue. -/
def real_abtcb (num_proc : Nat) (t : AbTCBPool) : AbTCBPool :=
  init_zmap num_proc (.AbTCBValid .DEAD (-1)) t

/-- `real_abq`: every queue empty. -/
def real_abq (num_chan : Nat) (q : AbQueuePool) : AbQueuePool :=
  init_zmap (num_chan + 1) (.AbQValid []) q

/-- **`tdqueue_init0_spec`**, with the allocation table in place of the owner
lists. -/
def tdqueue_init0_spec (num_proc num_chan kl kh : Nat) (mm : MALInit.MMTable) (size : Nat) (d : AData) :
    Option AData :=
  if d.init = false ∧ d.pg = false ∧ d.ipt = true then
    some { d with
      pg := true
      AT := MALInit.real_AT kl kh mm size d.AT
      nps := MALInit.real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := MPTInit.real_pt num_proc d.ptpool
      idpde := MPTInit.real_idpde d.idpde
      smspool := real_smspool num_proc d.smspool
      abtcb := real_abtcb num_proc d.abtcb
      abq := real_abq num_chan d.abq }
  else none

/-! ## The invariants (`AuxStateDataType.v`) -/

/-- `AbTCBCorrect`. -/
def AbTCBCorrect (num_chan : Nat) : AbTCB → Prop
  | .AbTCBUndef => False
  | .AbTCBValid _ b => -1 ≤ b ∧ b ≤ num_chan

def AbTCBCorrect_range (num_proc num_chan : Nat) (t : AbTCBPool) : Prop :=
  ∀ i, i < num_proc → AbTCBCorrect num_chan (t i)

/-- `AbQCorrect`. -/
def AbQCorrect (num_proc : Nat) : AbQueue → Prop
  | .AbQUndef => False
  | .AbQValid l => ∀ x, x ∈ l → x < num_proc

def AbQCorrect_range (num_proc num_chan : Nat) (q : AbQueuePool) : Prop :=
  ∀ i, i ≤ num_chan → AbQCorrect num_proc (q i)

/-- `NotInQ`: a thread without a container is on no queue. -/
def NotInQ (num_proc : Nat) (c : ContainerPool) (t : AbTCBPool) : Prop :=
  ∀ i s b, i < num_proc → (c i).cused = false → t i = .AbTCBValid s b → b = -1

/-- `QCount`: a thread is exactly once on the queue it says it is on. -/
def QCount (num_proc num_chan : Nat) (t : AbTCBPool) (q : AbQueuePool) : Prop :=
  ∀ i s b, i < num_proc → t i = .AbTCBValid s b → 0 ≤ b → b ≤ num_chan →
    ∃ l, q b.toNat = .AbQValid l ∧ l.count i = 1

/-- `InQ`: a thread on a queue's list says it is on that queue. -/
def InQ (num_proc num_chan : Nat) (t : AbTCBPool) (q : AbQueuePool) : Prop :=
  ∀ i j l, i < num_proc → j ≤ num_chan → q j = .AbQValid l → i ∈ l → ∃ s, t i = .AbTCBValid s j

/-! ## The relation between the two views (`AbQueueGen.v`) -/

/-- `abqueue_match_next_prev_rec l ending hd tl starting`: the list, tail
first, is linked through `prev` from `tl` back to `hd`. -/
def abqueue_match_next_prev_rec (num_proc : Nat) (tcb : TCBPool) : List Nat → Nat → Nat → Nat → Nat → Prop
  | [], _, hd, tl, _ => hd = num_proc ∧ tl = num_proc
  | [t], ending, hd, tl, starting => hd = t ∧ tl = t ∧ ∃ st, tcb t = .TCBValid st ending starting
  | t :: t' :: l', ending, hd, tl, starting => tl = t ∧ ∃ st prev, tcb t = .TCBValid st prev starting ∧
      abqueue_match_next_prev_rec num_proc tcb (t' :: l') ending hd prev t

def abqueue_match_dllist (num_proc num_chan : Nat) (abq : AbQueuePool) (tcb : TCBPool) (tdq : TDQueuePool) :
    Prop :=
  ∀ qi l, qi ≤ num_chan → abq qi = .AbQValid l →
    ∃ hd tl, tdq qi = .TDQValid hd tl ∧ abqueue_match_next_prev_rec num_proc tcb l num_proc hd tl num_proc

def abtcbpool_tcbpool (num_proc : Nat) (abtcb : AbTCBPool) (tcb : TCBPool) : Prop :=
  ∀ i tds inq, i < num_proc → abtcb i = .AbTCBValid tds inq → ∃ pv nx, tcb i = .TCBValid tds pv nx

/-- `AbQ_RealQ`. -/
structure AbQ_RealQ (num_proc num_chan : Nat) (abtcb : AbTCBPool) (abq : AbQueuePool) (tcb : TCBPool)
    (tdq : TDQueuePool) : Prop where
  dl : abqueue_match_dllist num_proc num_chan abq tcb tdq
  tp : abtcbpool_tcbpool num_proc abtcb tcb

/-! ## Links: the relation, restated -/

/-- `links e s l`: for each thread of `l`, the thread with its `prev` and its
`next`. `e` is the `prev` of the last, `s` the `next` of the first. -/
def links (e : Nat) : Nat → List Nat → List (Nat × Nat × Nat)
  | _, [] => []
  | s, t :: r => (t, r.headD e, s) :: links e t r

theorem links_mem {e : Nat} : ∀ {l : List Nat} {s x p nx : Nat}, (x, p, nx) ∈ links e s l → x ∈ l
  | [], _, _, _, _, h => by simp [links] at h
  | t :: r, s, x, p, nx, h => by
    rcases List.mem_cons.1 h with e1 | h'
    · cases e1; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (links_mem h')

theorem headD_append (l1 l2 : List Nat) (d : Nat) : (l1 ++ l2).headD d = l1.headD (l2.headD d) := by
  cases l1 <;> rfl

theorem getLastD_append (l1 l2 : List Nat) (d : Nat) : (l1 ++ l2).getLastD d = l2.getLastD (l1.getLastD d) := by
  induction l1 generalizing d with
  | nil => rfl
  | cons a r ih => rw [List.cons_append, List.getLastD_cons, ih, List.getLastD_cons]

/-- **Appending lists appends their links**: the last of the first list
points back to the head of the second, and the first of the second points on
to the last of the first. -/
theorem links_append (e : Nat) : ∀ (l1 l2 : List Nat) (s : Nat),
    links e s (l1 ++ l2) = links (l2.headD e) s l1 ++ links e (l1.getLastD s) l2
  | [], l2, s => rfl
  | t :: r, l2, s => by
    show (t, (r ++ l2).headD e, s) :: links e t (r ++ l2) =
      (t, r.headD (l2.headD e), s) :: (links (l2.headD e) t r ++ links e ((t :: r).getLastD s) l2)
    rw [links_append e r l2 t, headD_append, List.getLastD_cons]

/-- The links of a list ending in `x`. -/
theorem links_snoc (e s x : Nat) (r : List Nat) :
    links e s (r ++ [x]) = links x s r ++ [(x, e, r.getLastD s)] := links_append e r [x] s

/-- A list `l` (tail first) is the queue with head `hd` and tail `tl`. -/
def DL (np : Nat) (tcb : TCBPool) (l : List Nat) (hd tl : Nat) : Prop :=
  hd = l.getLastD np ∧ tl = l.headD np ∧
    ∀ x p nx, (x, p, nx) ∈ links np np l → ∃ st, tcb x = .TCBValid st p nx

/-- **The relation of mCertiKOS, restated through `links`.** -/
theorem rec_iff (np : Nat) (tcb : TCBPool) (e hd : Nat) : ∀ (l : List Nat) (tl s : Nat),
    abqueue_match_next_prev_rec np tcb l e hd tl s ↔
      (hd = l.getLastD np ∧ tl = l.headD np ∧
        ∀ x p nx, (x, p, nx) ∈ links e s l → ∃ st, tcb x = .TCBValid st p nx)
  | [], tl, s => by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, fun x p nx h => by simp [links] at h⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  | [t], tl, s => by
    constructor
    · rintro ⟨h1, h2, st, h3⟩
      refine ⟨h1, h2, fun x p nx h => ?_⟩
      rcases List.mem_cons.1 h with e1 | h'
      · cases e1; exact ⟨st, h3⟩
      · simp [links] at h'
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3 t e s List.mem_cons_self⟩
  | t :: t' :: l', tl, s => by
    have ih := rec_iff np tcb e hd (t' :: l')
    constructor
    · rintro ⟨h1, st, prev, h2, h3⟩
      obtain ⟨a1, a2, a3⟩ := (ih prev t).1 h3
      refine ⟨by rw [a1]; simp only [List.getLastD_cons], h1, fun x p nx h => ?_⟩
      rcases List.mem_cons.1 h with e1 | h'
      · cases e1
        have e2 : prev = t' := a2
        subst e2; exact ⟨st, h2⟩
      · exact a3 x p nx h'
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨st, hst⟩ := h3 t t' s List.mem_cons_self
      exact ⟨h2, st, t', hst, (ih t' t).2 ⟨by rw [h1]; simp only [List.getLastD_cons], rfl,
        fun x p nx h => h3 x p nx (List.mem_cons_of_mem _ h)⟩⟩

section DLLemmas
variable {np : Nat}

/-- Only the control blocks of the threads on the list matter. -/
theorem dl_frame {tcb tcb' : TCBPool} {l : List Nat} {hd tl : Nat} (h : DL np tcb l hd tl)
    (hf : ∀ x, x ∈ l → tcb' x = tcb x) : DL np tcb' l hd tl :=
  ⟨h.1, h.2.1, fun x p nx hm => by rw [hf x (links_mem hm)]; exact h.2.2 x p nx hm⟩

theorem dl_nil (tcb : TCBPool) : DL np tcb [] np np :=
  ⟨rfl, rfl, fun x p nx h => by simp [links] at h⟩

/-- Enqueue on an empty queue. -/
theorem dl_enq_nil {tcb : TCBPool} {hd tl : Nat} (h : DL np tcb [] hd tl) (i : Nat) (st : ThreadState) :
    tl = np ∧ DL np (setAt tcb i (.TCBValid st np np)) [i] i i := by
  refine ⟨h.2.1, rfl, rfl, fun x p nx hm => ?_⟩
  rcases List.mem_cons.1 hm with e1 | h'
  · cases e1; exact ⟨st, setAt_eq _ _ _⟩
  · simp [links] at h'

/-- Enqueue behind the tail `t`. -/
theorem dl_enq_cons {tcb : TCBPool} {t : Nat} {r : List Nat} {hd tl i : Nat} (h : DL np tcb (t :: r) hd tl)
    (hi : i ∉ t :: r) (hnd : (t :: r).Nodup) :
    tl = t ∧ ∃ st', tcb t = .TCBValid st' (r.headD np) np ∧ ∀ st,
      DL np (setAt (setAt tcb t (.TCBValid st' (r.headD np) i)) i (.TCBValid st t np)) (i :: t :: r) hd i := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨st', hst'⟩ := h3 t (r.headD np) np List.mem_cons_self
  have hit : i ≠ t := fun e => hi (e ▸ List.mem_cons_self)
  refine ⟨h2, st', hst', fun st => ⟨by rw [h1]; simp only [List.getLastD_cons], rfl, fun x p nx hm => ?_⟩⟩
  rcases List.mem_cons.1 hm with e1 | hm
  · cases e1; exact ⟨st, setAt_eq _ _ _⟩
  · rcases List.mem_cons.1 hm with e1 | hm
    · cases e1
      exact ⟨st', by rw [setAt_ne _ _ (Ne.symm hit), setAt_eq]⟩
    · have hx := links_mem hm
      have hxi : x ≠ i := fun e => hi (e ▸ List.mem_cons_of_mem _ hx)
      have hxt : x ≠ t := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hx)
      rw [setAt_ne _ _ hxi, setAt_ne _ _ hxt]
      exact h3 x p nx (List.mem_cons_of_mem _ hm)

/-- The head of the queue is the last of the list; its `next` is the one
before it. -/
theorem dl_last {tcb : TCBPool} {r : List Nat} {la hd tl : Nat} (h : DL np tcb (r ++ [la]) hd tl) :
    hd = la ∧ ∃ st, tcb la = .TCBValid st np (r.getLastD np) := by
  obtain ⟨h1, -, h3⟩ := h
  refine ⟨by rw [h1, List.getLastD_concat], h3 la np (r.getLastD np) ?_⟩
  rw [links_snoc]
  exact List.mem_append_right _ List.mem_cons_self

/-- The head `la` leaves a queue of two or more: `x`, next after it, becomes
the head. -/
theorem dl_deq_more {tcb : TCBPool} {r' : List Nat} {x la hd tl : Nat}
    (h : DL np tcb (r' ++ [x] ++ [la]) hd tl) (hnd : (r' ++ [x] ++ [la]).Nodup) :
    ∃ st', tcb x = .TCBValid st' la (r'.getLastD np) ∧
      DL np (setAt tcb x (.TCBValid st' np (r'.getLastD np))) (r' ++ [x]) x tl := by
  obtain ⟨h1, h2, h3⟩ := h
  have hl : links np np (r' ++ [x] ++ [la]) =
      (links x np r' ++ [(x, la, r'.getLastD np)]) ++ [(la, np, (r' ++ [x]).getLastD np)] := by
    rw [links_snoc, links_snoc]
  rw [hl] at h3
  obtain ⟨st', hst'⟩ := h3 x la (r'.getLastD np)
    (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
  have hxr : ∀ a, a ∈ r' → a ≠ x := fun a ha =>
    (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 a ha x List.mem_cons_self
  refine ⟨st', hst', by rw [List.getLastD_concat], ?_, fun y p nx hm => ?_⟩
  · rw [h2]; simp only [headD_append, List.headD_cons]
  · rw [links_snoc] at hm
    rcases List.mem_append.1 hm with hm | hm
    · rw [setAt_ne _ _ (hxr y (links_mem hm))]
      exact h3 y p nx (List.mem_append_left _ (List.mem_append_left _ hm))
    · rcases List.mem_cons.1 hm with e1 | hm
      · cases e1; exact ⟨st', setAt_eq _ _ _⟩
      · simp at hm

/-- The control block of a thread in the middle of the list. -/
theorem dl_mid {tcb : TCBPool} {l1 l2 : List Nat} {i hd tl : Nat} (h : DL np tcb (l1 ++ i :: l2) hd tl) :
    ∃ st, tcb i = .TCBValid st (l2.headD np) (l1.getLastD np) := by
  refine h.2.2 i (l2.headD np) (l1.getLastD np) ?_
  rw [links_append]
  exact List.mem_append_right _ List.mem_cons_self

/-- The tail `i` leaves a queue of two or more: `y`, before it, becomes the
tail. -/
theorem dl_rmv_tail {tcb : TCBPool} {y : Nat} {l2' : List Nat} {i hd tl : Nat}
    (h : DL np tcb (i :: y :: l2') hd tl) (hnd : (i :: y :: l2').Nodup) :
    ∃ st0, tcb y = .TCBValid st0 (l2'.headD np) i ∧
      DL np (setAt tcb y (.TCBValid st0 (l2'.headD np) np)) (y :: l2') hd y := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨st0, hst0⟩ := h3 y (l2'.headD np) i (List.mem_cons_of_mem _ List.mem_cons_self)
  have hy : ∀ a, a ∈ l2' → a ≠ y := fun a ha e =>
    (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1 (e ▸ ha)
  refine ⟨st0, hst0, by rw [h1]; simp only [List.getLastD_cons], rfl, fun x p nx hm => ?_⟩
  rcases List.mem_cons.1 hm with e1 | hm
  · cases e1; exact ⟨st0, setAt_eq _ _ _⟩
  · rw [setAt_ne _ _ (hy x (links_mem hm))]
    exact h3 x p nx (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))

/-- `i` leaves the middle of a queue: `y` before it and `x` after it are
linked to each other. -/
theorem dl_rmv_mid {tcb : TCBPool} {l1' l2' : List Nat} {x y i hd tl : Nat}
    (h : DL np tcb (l1' ++ [x] ++ i :: y :: l2') hd tl) (hnd : (l1' ++ [x] ++ i :: y :: l2').Nodup) :
    ∃ st0 st1, tcb y = .TCBValid st0 (l2'.headD np) i ∧ tcb x = .TCBValid st1 i (l1'.getLastD np) ∧ x ≠ y ∧
      DL np (setAt (setAt tcb y (.TCBValid st0 (l2'.headD np) x)) x (.TCBValid st1 y (l1'.getLastD np)))
        (l1' ++ [x] ++ y :: l2') hd tl := by
  obtain ⟨h1, h2, h3⟩ := h
  have hl : links np np (l1' ++ [x] ++ i :: y :: l2') =
      (links x np l1' ++ [(x, i, l1'.getLastD np)]) ++ ((i, y, x) :: (y, l2'.headD np, i) :: links np y l2') := by
    rw [links_append, links_snoc, List.getLastD_concat]; rfl
  rw [hl] at h3
  obtain ⟨st0, hst0⟩ := h3 y (l2'.headD np) i
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨st1, hst1⟩ := h3 x i (l1'.getLastD np)
    (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
  obtain ⟨hn1, hn2, hn3⟩ := List.nodup_append.1 hnd
  have hxy : x ≠ y := hn3 x (List.mem_append_right _ List.mem_cons_self) y
    (List.mem_cons_of_mem _ List.mem_cons_self)
  have h1x : ∀ a, a ∈ l1' → a ≠ x := fun a ha => (List.nodup_append.1 hn1).2.2 a ha x List.mem_cons_self
  have h1y : ∀ a, a ∈ l1' → a ≠ y := fun a ha =>
    hn3 a (List.mem_append_left _ ha) y (List.mem_cons_of_mem _ List.mem_cons_self)
  have h2x : ∀ a, a ∈ l2' → a ≠ x := fun a ha e =>
    hn3 x (List.mem_append_right _ List.mem_cons_self) a
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)) e.symm
  have h2y : ∀ a, a ∈ l2' → a ≠ y := fun a ha e =>
    (List.nodup_cons.1 (List.nodup_cons.1 hn2).2).1 (e ▸ ha)
  refine ⟨st0, st1, hst0, hst1, hxy, ?_, ?_, fun z p nx hm => ?_⟩
  · rw [h1]; simp only [getLastD_append, List.getLastD_cons]
  · rw [h2]; simp only [headD_append, List.headD_cons]
  · have hl' : links np np (l1' ++ [x] ++ y :: l2') =
        (links x np l1' ++ [(x, y, l1'.getLastD np)]) ++ ((y, l2'.headD np, x) :: links np y l2') := by
      rw [links_append, links_snoc, List.getLastD_concat]; rfl
    rw [hl'] at hm
    rcases List.mem_append.1 hm with hm | hm
    · rcases List.mem_append.1 hm with hm | hm
      · have hz := links_mem hm
        rw [setAt_ne _ _ (h1x z hz), setAt_ne _ _ (h1y z hz)]
        exact h3 z p nx (List.mem_append_left _ (List.mem_append_left _ hm))
      · rcases List.mem_cons.1 hm with e1 | hm
        · cases e1; exact ⟨st1, setAt_eq _ _ _⟩
        · simp at hm
    · rcases List.mem_cons.1 hm with e1 | hm
      · cases e1
        exact ⟨st0, by rw [setAt_ne _ _ (Ne.symm hxy), setAt_eq]⟩
      · have hz := links_mem hm
        rw [setAt_ne _ _ (h2x z hz), setAt_ne _ _ (h2y z hz)]
        exact h3 z p nx (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))

end DLLemmas

/-! ## What the invariants give -/

section Pool
variable {np nc : Nat}

theorem q_lt {abq : AbQueuePool} (hQC : AbQCorrect_range np nc abq) {n : Nat} {l : List Nat} (hn : n ≤ nc)
    (hl : abq n = .AbQValid l) {x : Nat} (hx : x ∈ l) : x < np := by
  have := hQC n hn; rw [hl] at this; exact this x hx

/-- A queue lists no thread twice. -/
theorem q_nodup {abtcb : AbTCBPool} {abq : AbQueuePool} (hQC : AbQCorrect_range np nc abq)
    (hCnt : QCount np nc abtcb abq) (hIn : InQ np nc abtcb abq) {n : Nat} {l : List Nat} (hn : n ≤ nc)
    (hl : abq n = .AbQValid l) : l.Nodup := by
  rw [List.nodup_iff_count]
  intro x
  by_cases hx : x ∈ l
  · have hxl := q_lt hQC hn hl hx
    obtain ⟨s, hs⟩ := hIn x n l hxl hn hl hx
    obtain ⟨l', hl', hc⟩ := hCnt x s n hxl hs (by omega) (by omega)
    have e : ((n : Int)).toNat = n := by omega
    rw [e, hl] at hl'; cases hl'
    omega
  · rw [List.count_eq_zero_of_not_mem hx]; omega

/-- A thread is on one queue only. -/
theorem q_disjoint {abtcb : AbTCBPool} {abq : AbQueuePool} (hQC : AbQCorrect_range np nc abq)
    (hIn : InQ np nc abtcb abq) {n qi : Nat} {l l' : List Nat} {x : Nat} (hn : n ≤ nc) (hqi : qi ≤ nc)
    (hne : qi ≠ n) (hl : abq n = .AbQValid l) (hl' : abq qi = .AbQValid l') (hx : x ∈ l) : x ∉ l' := by
  intro hx'
  have hxl := q_lt hQC hn hl hx
  obtain ⟨s, hs⟩ := hIn x n l hxl hn hl hx
  obtain ⟨s', hs'⟩ := hIn x qi l' hxl hqi hl' hx'
  rw [hs] at hs'
  injection hs' with e1 e2
  omega

/-- The control blocks keep their states. -/
def SameSt (tcb tcb' : TCBPool) : Prop :=
  ∀ i tds pv nx, tcb i = .TCBValid tds pv nx → ∃ pv' nx', tcb' i = .TCBValid tds pv' nx'

theorem SameSt.refl (tcb : TCBPool) : SameSt tcb tcb := fun _ _ pv nx h => ⟨pv, nx, h⟩

theorem SameSt.set {tcb tcb' : TCBPool} (h : SameSt tcb tcb') {j : Nat} {ts : ThreadState} {p nx : Nat}
    (hj : tcb j = .TCBValid ts p nx) (p' nx' : Nat) : SameSt tcb (setAt tcb' j (.TCBValid ts p' nx')) := by
  intro i tds pv nx0 hi
  by_cases e : i = j
  · subst e
    rw [hj] at hi; cases hi
    exact ⟨_, _, setAt_eq _ _ _⟩
  · obtain ⟨pv', nx'', h'⟩ := h i tds pv nx0 hi
    exact ⟨pv', nx'', by rw [setAt_ne _ _ e]; exact h'⟩

theorem sameA_set {abtcb : AbTCBPool} {j : Nat} {st : ThreadState} {b : Int} (hj : abtcb j = .AbTCBValid st b)
    (b' : Int) : ∀ i tds inq, i < np → setAt abtcb j (.AbTCBValid st b') i = .AbTCBValid tds inq →
      ∃ inq0, abtcb i = .AbTCBValid tds inq0 := by
  intro i tds inq _ h
  by_cases e : i = j
  · subst e
    rw [setAt_eq] at h
    injection h with e1 e2
    subst e1; exact ⟨b, hj⟩
  · rw [setAt_ne _ _ e] at h; exact ⟨inq, h⟩

theorem tp_update {abtcb abtcb' : AbTCBPool} {tcb tcb' : TCBPool} (h : abtcbpool_tcbpool np abtcb tcb)
    (ha : ∀ i tds inq, i < np → abtcb' i = .AbTCBValid tds inq → ∃ inq0, abtcb i = .AbTCBValid tds inq0)
    (hc : SameSt tcb tcb') : abtcbpool_tcbpool np abtcb' tcb' := by
  intro i tds inq hi he
  obtain ⟨inq0, h0⟩ := ha i tds inq hi he
  obtain ⟨pv, nx, h1⟩ := h i tds inq0 hi h0
  exact hc i tds pv nx h1

/-- **One queue changes.** The relation survives if the new list matches the
new pointers, and the control blocks that changed are on no other queue. -/
theorem realQ_update {abtcb abtcb' : AbTCBPool} {abq : AbQueuePool} {tcb tcb' : TCBPool}
    {tdq tdq' : TDQueuePool} (hR : AbQ_RealQ np nc abtcb abq tcb tdq) {n : Nat} {l' : List Nat}
    {hd' tl' : Nat} (htq : tdq' n = .TDQValid hd' tl') (hto : ∀ qi, qi ≠ n → tdq' qi = tdq qi)
    (hdl : DL np tcb' l' hd' tl')
    (hother : ∀ qi l x, qi ≤ nc → qi ≠ n → abq qi = .AbQValid l → x ∈ l → tcb' x = tcb x)
    (htp : abtcbpool_tcbpool np abtcb' tcb') :
    AbQ_RealQ np nc abtcb' (setAt abq n (.AbQValid l')) tcb' tdq' := by
  refine ⟨fun qi l hqi hl => ?_, htp⟩
  by_cases e : qi = n
  · subst e
    rw [setAt_eq] at hl
    cases hl
    exact ⟨hd', tl', htq, (rec_iff np tcb' np hd' l' tl' np).2 hdl⟩
  · rw [setAt_ne _ _ e] at hl
    obtain ⟨hd, tl, h1, h2⟩ := hR.dl qi l hqi hl
    exact ⟨hd, tl, (hto qi e).trans h1, (rec_iff np tcb' np hd l tl np).2
      (dl_frame ((rec_iff np tcb np hd l tl np).1 h2) (fun x hx => hother qi l x hqi e hl hx))⟩

theorem remove_notin {x : Nat} {l : List Nat} (h : x ∉ l) : remove x l = l :=
  List.filter_eq_self.2 (fun a ha => bne_iff_ne.2 (fun e => h (e ▸ ha)))

theorem remove_mid {x : Nat} {l1 l2 : List Nat} (h1 : x ∉ l1) (h2 : x ∉ l2) :
    remove x (l1 ++ x :: l2) = l1 ++ l2 := by
  have e : remove x (l1 ++ x :: l2) = remove x l1 ++ remove x (x :: l2) := List.filter_append _ _
  have e2 : remove x (x :: l2) = remove x l2 := by simp [remove]
  rw [e, e2, remove_notin h1, remove_notin h2]

/-- `real_data`: the initial states are related. -/
theorem real_data (abtcb : AbTCBPool) (abq : AbQueuePool) (tcb : TCBPool) (tdq : TDQueuePool) :
    AbQ_RealQ np nc (real_abtcb np abtcb) (real_abq nc abq) (real_tcb np tcb) (real_tdq np nc tdq) := by
  constructor
  · intro qi l hqi hl
    unfold real_abq at hl
    rw [init_zmap_inside _ _ _ _ (by omega)] at hl
    cases hl
    exact ⟨np, np, by unfold real_tdq; rw [init_zmap_inside _ _ _ _ (by omega)], rfl, rfl⟩
  · intro i tds inq hi he
    unfold real_abtcb at he
    rw [init_zmap_inside _ _ _ _ hi] at he
    injection he with e1 e2
    subst e1
    exact ⟨np, np, by unfold real_tcb; rw [init_zmap_inside _ _ _ _ hi]⟩

end Pool

/-! ## The pointer specifications, evaluated -/

section Eval
variable {np nc : Nat}

theorem enqueue_spec_nil {d : QData} {n i h t : Nat} {st : ThreadState} {p nx : Nat} (hpg : d.pg = true)
    (hipt : d.ipt = true) (hn : n ≤ nc) (hi : i < np) (hq : d.tdq n = .TDQValid h t)
    (hti : d.tcb i = .TCBValid st p nx) (ht : t = np) :
    enqueue_spec np nc n i d = some { d with
      tcb := setAt d.tcb i (.TCBValid st np np)
      tdq := setAt d.tdq n (.TDQValid i i) } := by
  unfold enqueue_spec
  rw [if_pos ⟨hpg, hipt, hn, hi⟩, hq, hti]
  simp only
  rw [if_pos ht]

theorem enqueue_spec_cons {d : QData} {n i h t : Nat} {st : ThreadState} {p nx : Nat} (hpg : d.pg = true)
    (hipt : d.ipt = true) (hn : n ≤ nc) (hi : i < np) (hq : d.tdq n = .TDQValid h t)
    (hti : d.tcb i = .TCBValid st p nx) (ht : t < np) {st' : ThreadState} {p' nx' : Nat}
    (htt : d.tcb t = .TCBValid st' p' nx') :
    enqueue_spec np nc n i d = some { d with
      tcb := setAt (setAt d.tcb t (.TCBValid st' p' i)) i (.TCBValid st t np)
      tdq := setAt d.tdq n (.TDQValid h i) } := by
  unfold enqueue_spec
  rw [if_pos ⟨hpg, hipt, hn, hi⟩, hq, hti]
  simp only
  rw [if_neg (Nat.ne_of_lt ht), if_pos ht, htt]

theorem dequeue_spec_empty {d : QData} {n h t : Nat} (hpg : d.pg = true) (hipt : d.ipt = true) (hn : n ≤ nc)
    (hq : d.tdq n = .TDQValid h t) (hh : h = np) : dequeue_spec np nc n d = some (d, np) := by
  unfold dequeue_spec
  rw [if_pos ⟨hpg, hipt, hn⟩, hq]
  simp only
  rw [if_pos hh]

theorem dequeue_spec_one {d : QData} {n h t : Nat} (hpg : d.pg = true) (hipt : d.ipt = true) (hn : n ≤ nc)
    (hq : d.tdq n = .TDQValid h t) (hh : h < np) {st : ThreadState} {p nx : Nat}
    (hth : d.tcb h = .TCBValid st p nx) (hx : nx = np) :
    dequeue_spec np nc n d = some ({ d with tdq := setAt d.tdq n (.TDQValid np np) }, h) := by
  unfold dequeue_spec
  rw [if_pos ⟨hpg, hipt, hn⟩, hq]
  simp only
  rw [if_neg (Nat.ne_of_lt hh), if_pos hh, hth]
  simp only
  rw [if_pos hx]

theorem dequeue_spec_more {d : QData} {n h t : Nat} (hpg : d.pg = true) (hipt : d.ipt = true) (hn : n ≤ nc)
    (hq : d.tdq n = .TDQValid h t) (hh : h < np) {st : ThreadState} {p nx : Nat}
    (hth : d.tcb h = .TCBValid st p nx) (hx : nx ≠ np) {st' : ThreadState} {p' nx' : Nat}
    (htn : d.tcb nx = .TCBValid st' p' nx') :
    dequeue_spec np nc n d = some ({ d with
      tcb := setAt d.tcb nx (.TCBValid st' np nx')
      tdq := setAt d.tdq n (.TDQValid nx t) }, h) := by
  unfold dequeue_spec
  rw [if_pos ⟨hpg, hipt, hn⟩, hq]
  simp only
  rw [if_neg (Nat.ne_of_lt hh), if_pos hh, hth]
  simp only
  rw [if_neg hx, htn]

/-- `i` is alone on the queue. -/
theorem queue_rmv_spec_A {d : QData} {n i h t : Nat} {st : ThreadState} {pv nx : Nat} (hpg : d.pg = true)
    (hipt : d.ipt = true) (hn : n ≤ nc) (hi : i < np) (hti : d.tcb i = .TCBValid st pv nx)
    (hq : d.tdq n = .TDQValid h t) (h1 : pv = np) (h2 : nx = np) :
    queue_rmv_spec np nc n i d = some { d with tdq := setAt d.tdq n (.TDQValid np np) } := by
  unfold queue_rmv_spec
  rw [if_pos ⟨hpg, hipt, hn, hi⟩, hti, hq]
  simp only
  rw [if_pos h1, if_pos h2]

/-- `i` is the head and not the tail. -/
theorem queue_rmv_spec_B {d : QData} {n i h t : Nat} {st : ThreadState} {pv nx : Nat} (hpg : d.pg = true)
    (hipt : d.ipt = true) (hn : n ≤ nc) (hi : i < np) (hti : d.tcb i = .TCBValid st pv nx)
    (hq : d.tdq n = .TDQValid h t) (h1 : pv = np) (h2 : nx ≠ np) {st1 : ThreadState} {p1 nx1 : Nat}
    (htn : d.tcb nx = .TCBValid st1 p1 nx1) :
    queue_rmv_spec np nc n i d = some { d with
      tcb := setAt d.tcb nx (.TCBValid st1 np nx1)
      tdq := setAt d.tdq n (.TDQValid nx t) } := by
  unfold queue_rmv_spec
  rw [if_pos ⟨hpg, hipt, hn, hi⟩, hti, hq]
  simp only
  rw [if_pos h1, if_neg h2, htn]

/-- `i` is the tail and not the head. -/
theorem queue_rmv_spec_C {d : QData} {n i h t : Nat} {st : ThreadState} {pv nx : Nat} (hpg : d.pg = true)
    (hipt : d.ipt = true) (hn : n ≤ nc) (hi : i < np) (hti : d.tcb i = .TCBValid st pv nx)
    (hq : d.tdq n = .TDQValid h t) (h1 : pv ≠ np) {st0 : ThreadState} {p0 nx0 : Nat}
    (htp : d.tcb pv = .TCBValid st0 p0 nx0) (h2 : nx = np) :
    queue_rmv_spec np nc n i d = some { d with
      tcb := setAt d.tcb pv (.TCBValid st0 p0 np)
      tdq := setAt d.tdq n (.TDQValid h pv) } := by
  unfold queue_rmv_spec
  rw [if_pos ⟨hpg, hipt, hn, hi⟩, hti, hq]
  simp only
  rw [if_neg h1, htp]
  simp only
  rw [if_pos h2]

/-- `i` is in the middle. -/
theorem queue_rmv_spec_D {d : QData} {n i h t : Nat} {st : ThreadState} {pv nx : Nat} (hpg : d.pg = true)
    (hipt : d.ipt = true) (hn : n ≤ nc) (hi : i < np) (hti : d.tcb i = .TCBValid st pv nx)
    (hq : d.tdq n = .TDQValid h t) (h1 : pv ≠ np) {st0 : ThreadState} {p0 nx0 : Nat}
    (htp : d.tcb pv = .TCBValid st0 p0 nx0) (h2 : nx ≠ np) {st1 : ThreadState} {p1 nx1 : Nat}
    (htn : d.tcb nx = .TCBValid st1 p1 nx1) :
    queue_rmv_spec np nc n i d = some { d with
      tcb := setAt (setAt d.tcb pv (.TCBValid st0 p0 nx)) nx (.TCBValid st1 pv nx1) } := by
  unfold queue_rmv_spec
  rw [if_pos ⟨hpg, hipt, hn, hi⟩, hti, hq]
  simp only
  rw [if_neg h1, htp]
  simp only
  rw [if_neg h2, htn]

end Eval

end PAbQueue
