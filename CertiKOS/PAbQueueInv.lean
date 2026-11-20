import CertiKOS.PAbQueueGen

/-!
# mCertiKOS `PAbQueue`: its invariants, and its code

* `AInv`: the invariants of the list view (`valid_TCB`, `valid_TDQ`,
  `valid_notinQ`, `valid_count`, `valid_inQ` of `proc/PAbQueue.v`).
* `real_ainv`, `set_state0_keeps`, `enqueue0_keeps`, `dequeue0_keeps`,
  `queue_rmv0_keeps`: **initialisation establishes them and every operation
  keeps them** (`tdqueue_init_inv`, `set_state_inv`, `enqueue_inv`,
  `dequeue_inv`, `queue_rmv_inv`).
* `RelA`, `MatchA`: the region seen as lists.
* `getState0_triple`, `setState0_triple`, `enqueue0_triple`,
  `dequeue0_triple`, `queueRmv0_triple`: **the C code refines the list
  specifications.** Each is the triple of the layer below, carried across the
  relation by `Triple.sim` and the theorems of `PAbQueueGen.lean`.
* `real_relA`: the initial states are related.

After this file a caller sees threads and queues only as `abtcb` and `abq`.

Not done here: the primitives of the layers below `PQueueInit` (page tables,
shared memory) are not yet restated over `AData`.
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

/-! ## The invariants -/

/-- The invariants of the list view. -/
structure AInv (np nc : Nat) (a : AData) : Prop where
  tc : AbTCBCorrect_range np nc a.abtcb
  qc : AbQCorrect_range np nc a.abq
  niq : NotInQ np a.AC a.abtcb
  cnt : QCount np nc a.abtcb a.abq
  inq : InQ np nc a.abtcb a.abq

section Pools
variable {np nc : Nat}

theorem count_remove_ne {j x : Nat} (h : j ≠ x) : ∀ l : List Nat, (remove x l).count j = l.count j
  | [] => rfl
  | y :: l => by
    have ih := count_remove_ne h l
    unfold remove at ih ⊢
    rw [List.filter_cons]
    by_cases e : y = x
    · subst e
      have e1 : (y != y) = false := by simp
      rw [e1, if_neg (by simp), ih, List.count_cons_of_ne (fun e' => h e'.symm)]
    · have e1 : (y != x) = true := bne_iff_ne.2 e
      rw [if_pos e1, List.count_cons, List.count_cons, ih]

/-- The state of a thread changes, not its queue. -/
theorem setst_inv {abtcb : AbTCBPool} {abq : AbQueuePool} {c : ContainerPool} {n : Nat}
    {st st' : ThreadState} {b : Int} (ha : abtcb n = .AbTCBValid st b)
    (h1 : AbTCBCorrect_range np nc abtcb) (h3 : NotInQ np c abtcb) (h4 : QCount np nc abtcb abq)
    (h5 : InQ np nc abtcb abq) :
    AbTCBCorrect_range np nc (setAt abtcb n (.AbTCBValid st' b)) ∧
    NotInQ np c (setAt abtcb n (.AbTCBValid st' b)) ∧
    QCount np nc (setAt abtcb n (.AbTCBValid st' b)) abq ∧
    InQ np nc (setAt abtcb n (.AbTCBValid st' b)) abq := by
  have back : ∀ j s b', setAt abtcb n (.AbTCBValid st' b) j = .AbTCBValid s b' →
      ∃ s0, abtcb j = .AbTCBValid s0 b' := by
    intro j s b' h
    by_cases e : j = n
    · subst e
      rw [setAt_eq] at h
      injection h with e1 e2
      subst e2; exact ⟨st, ha⟩
    · rw [setAt_ne _ _ e] at h; exact ⟨s, h⟩
  have fwd : ∀ j s b', abtcb j = .AbTCBValid s b' →
      ∃ s', setAt abtcb n (.AbTCBValid st' b) j = .AbTCBValid s' b' := by
    intro j s b' h
    by_cases e : j = n
    · subst e
      rw [ha] at h
      injection h with e1 e2
      subst e2; exact ⟨st', setAt_eq _ _ _⟩
    · exact ⟨s, by rw [setAt_ne _ _ e]; exact h⟩
  refine ⟨fun j hj => ?_, fun j s b' hj hc h => ?_, fun j s b' hj h hb0 hb1 => ?_,
    fun j qi l hj hqi hl hm => ?_⟩
  · have := h1 j hj
    cases hj' : abtcb j with
    | AbTCBUndef => rw [hj'] at this; exact this.elim
    | AbTCBValid s b' =>
      rw [hj'] at this
      obtain ⟨s', hs'⟩ := fwd j s b' hj'
      rw [hs']; exact this
  · obtain ⟨s0, h0⟩ := back j s b' h
    exact h3 j s0 b' hj hc h0
  · obtain ⟨s0, h0⟩ := back j s b' h
    exact h4 j s0 b' hj h0 hb0 hb1
  · obtain ⟨s, hs⟩ := h5 j qi l hj hqi hl hm
    exact fwd j s qi hs

/-- A thread on no queue joins queue `n`. -/
theorem enq_inv {abtcb : AbTCBPool} {abq : AbQueuePool} {c : ContainerPool} {n i : Nat} {l : List Nat}
    {st : ThreadState} (hn : n ≤ nc) (hi : i < np) (hl : abq n = .AbQValid l)
    (hai : abtcb i = .AbTCBValid st (-1)) (hcu : (c i).cused = true)
    (h1 : AbTCBCorrect_range np nc abtcb) (h2 : AbQCorrect_range np nc abq) (h3 : NotInQ np c abtcb)
    (h4 : QCount np nc abtcb abq) (h5 : InQ np nc abtcb abq) :
    AbTCBCorrect_range np nc (setAt abtcb i (.AbTCBValid st n)) ∧
    AbQCorrect_range np nc (setAt abq n (.AbQValid (i :: l))) ∧
    NotInQ np c (setAt abtcb i (.AbTCBValid st n)) ∧
    QCount np nc (setAt abtcb i (.AbTCBValid st n)) (setAt abq n (.AbQValid (i :: l))) ∧
    InQ np nc (setAt abtcb i (.AbTCBValid st n)) (setAt abq n (.AbQValid (i :: l))) := by
  have hnot : ∀ qi l', qi ≤ nc → abq qi = .AbQValid l' → i ∉ l' := by
    intro qi l' hqi hl' hmem
    obtain ⟨s, hs'⟩ := h5 i qi l' hi hqi hl' hmem
    rw [hai] at hs'
    injection hs' with e1 e2
    omega
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j s b hj hc h => ?_, fun j s b hj h hb0 hb1 => ?_,
    fun j qi l' hj hqi hl' hm => ?_⟩
  · by_cases e : j = i
    · subst e; rw [setAt_eq]; exact ⟨by omega, by omega⟩
    · rw [setAt_ne _ _ e]; exact h1 j hj
  · by_cases e : j = n
    · subst e
      rw [setAt_eq]
      intro x hx
      rcases List.mem_cons.1 hx with e1 | hx
      · rw [e1]; exact hi
      · exact q_lt h2 hn hl hx
    · rw [setAt_ne _ _ e]; exact h2 j hj
  · by_cases e : j = i
    · subst e; rw [hcu] at hc; cases hc
    · rw [setAt_ne _ _ e] at h; exact h3 j s b hj hc h
  · by_cases e : j = i
    · subst e
      rw [setAt_eq] at h
      injection h with e1 e2
      subst e2
      have e3 : ((n : Int)).toNat = n := by omega
      refine ⟨j :: l, by rw [e3, setAt_eq], ?_⟩
      rw [List.count_cons_self, List.count_eq_zero_of_not_mem (hnot n l hn hl)]
    · rw [setAt_ne _ _ e] at h
      obtain ⟨l0, hl0, hc0⟩ := h4 j s b hj h hb0 hb1
      by_cases e2 : b.toNat = n
      · rw [e2, hl] at hl0
        cases hl0
        refine ⟨i :: l, by rw [e2, setAt_eq], ?_⟩
        rw [List.count_cons_of_ne (fun e' => e e'.symm)]; exact hc0
      · exact ⟨l0, by rw [setAt_ne _ _ e2]; exact hl0, hc0⟩
  · by_cases e : qi = n
    · subst e
      rw [setAt_eq] at hl'
      cases hl'
      by_cases e2 : j = i
      · subst e2; exact ⟨st, setAt_eq _ _ _⟩
      · rcases List.mem_cons.1 hm with e3 | hm
        · exact absurd e3 e2
        · obtain ⟨s, hs⟩ := h5 j qi l hj hqi hl hm
          exact ⟨s, by rw [setAt_ne _ _ e2]; exact hs⟩
    · rw [setAt_ne _ _ e] at hl'
      obtain ⟨s, hs⟩ := h5 j qi l' hj hqi hl' hm
      have e2 : j ≠ i := fun e' => hnot qi l' hqi hl' (e' ▸ hm)
      exact ⟨s, by rw [setAt_ne _ _ e2]; exact hs⟩

/-- A thread on queue `n` leaves it. -/
theorem rmv_inv {abtcb : AbTCBPool} {abq : AbQueuePool} {c : ContainerPool} {n x : Nat} {l : List Nat}
    {st : ThreadState} (hn : n ≤ nc) (hx : x < np) (hl : abq n = .AbQValid l)
    (hax : abtcb x = .AbTCBValid st n)
    (h1 : AbTCBCorrect_range np nc abtcb) (h2 : AbQCorrect_range np nc abq) (h3 : NotInQ np c abtcb)
    (h4 : QCount np nc abtcb abq) (h5 : InQ np nc abtcb abq) :
    AbTCBCorrect_range np nc (setAt abtcb x (.AbTCBValid st (-1))) ∧
    AbQCorrect_range np nc (setAt abq n (.AbQValid (remove x l))) ∧
    NotInQ np c (setAt abtcb x (.AbTCBValid st (-1))) ∧
    QCount np nc (setAt abtcb x (.AbTCBValid st (-1))) (setAt abq n (.AbQValid (remove x l))) ∧
    InQ np nc (setAt abtcb x (.AbTCBValid st (-1))) (setAt abq n (.AbQValid (remove x l))) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j s b hj hc h => ?_, fun j s b hj h hb0 hb1 => ?_,
    fun j qi l' hj hqi hl' hm => ?_⟩
  · by_cases e : j = x
    · subst e; rw [setAt_eq]; exact ⟨by omega, by omega⟩
    · rw [setAt_ne _ _ e]; exact h1 j hj
  · by_cases e : j = n
    · subst e
      rw [setAt_eq]
      intro y hy
      exact q_lt h2 hn hl (List.mem_filter.1 hy).1
    · rw [setAt_ne _ _ e]; exact h2 j hj
  · by_cases e : j = x
    · subst e
      rw [setAt_eq] at h
      injection h with e1 e2
      exact e2.symm
    · rw [setAt_ne _ _ e] at h; exact h3 j s b hj hc h
  · by_cases e : j = x
    · subst e
      rw [setAt_eq] at h
      injection h with e1 e2
      omega
    · rw [setAt_ne _ _ e] at h
      obtain ⟨l0, hl0, hc0⟩ := h4 j s b hj h hb0 hb1
      by_cases e2 : b.toNat = n
      · rw [e2, hl] at hl0
        cases hl0
        exact ⟨remove x l, by rw [e2, setAt_eq], by rw [count_remove_ne e]; exact hc0⟩
      · exact ⟨l0, by rw [setAt_ne _ _ e2]; exact hl0, hc0⟩
  · by_cases e : qi = n
    · subst e
      rw [setAt_eq] at hl'
      cases hl'
      obtain ⟨hm1, hm2⟩ := List.mem_filter.1 hm
      have e2 : j ≠ x := bne_iff_ne.1 hm2
      obtain ⟨s, hs⟩ := h5 j qi l hj hqi hl hm1
      exact ⟨s, by rw [setAt_ne _ _ e2]; exact hs⟩
    · rw [setAt_ne _ _ e] at hl'
      obtain ⟨s, hs⟩ := h5 j qi l' hj hqi hl' hm
      have e2 : j ≠ x := by
        intro e'
        subst e'
        rw [hax] at hs
        injection hs with e3 e4
        omega
      exact ⟨s, by rw [setAt_ne _ _ e2]; exact hs⟩

end Pools

section Keeps
variable {np nc : Nat}

/-- **Initialisation establishes the invariants**, whatever the containers. -/
theorem real_ainv (c : ContainerPool) (abtcb : AbTCBPool) (abq : AbQueuePool) :
    AbTCBCorrect_range np nc (real_abtcb np abtcb) ∧ AbQCorrect_range np nc (real_abq nc abq) ∧
    NotInQ np c (real_abtcb np abtcb) ∧ QCount np nc (real_abtcb np abtcb) (real_abq nc abq) ∧
    InQ np nc (real_abtcb np abtcb) (real_abq nc abq) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j s b hj _ h => ?_, fun j s b hj h hb0 _ => ?_,
    fun j qi l _ hqi hl hm => ?_⟩
  · unfold real_abtcb; rw [init_zmap_inside _ _ _ _ hj]; exact ⟨by omega, by omega⟩
  · unfold real_abq; rw [init_zmap_inside _ _ _ _ (by omega)]; intro x hx; cases hx
  · unfold real_abtcb at h
    rw [init_zmap_inside _ _ _ _ hj] at h
    injection h with e1 e2
    exact e2.symm
  · unfold real_abtcb at h
    rw [init_zmap_inside _ _ _ _ hj] at h
    injection h with e1 e2
    omega
  · unfold real_abq at hl
    rw [init_zmap_inside _ _ _ _ (by omega)] at hl
    cases hl
    cases hm

/-- **`tdqueue_init0_spec` establishes the invariants.** -/
theorem tdqueue_init0_inv {kl kh : Nat} {mm : MALInit.MMTable} {size : Nat} {a a' : AData}
    (hs : tdqueue_init0_spec np nc kl kh mm size a = some a') : AInv np nc a' := by
  unfold tdqueue_init0_spec at hs
  by_cases hc : a.init = false ∧ a.pg = false ∧ a.ipt = true
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := real_ainv (np := np) (nc := nc) (real_AC kl kh mm size) a.abtcb a.abq
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`set_state0_spec` keeps the invariants.** -/
theorem set_state0_keeps {num_id n s : Nat} {a a' : AData} (hs : set_state0_spec num_id n s a = some a')
    (hI : AInv np nc a) : AInv np nc a' := by
  unfold set_state0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n < num_id
  · rw [if_pos hc] at hs
    by_cases hcu : (a.AC n).cused = true
    · rw [if_pos hcu] at hs
      cases hai : a.abtcb n with
      | AbTCBUndef => rw [hai] at hs; cases hs
      | AbTCBValid st b =>
        cases hz : ZtoThreadState s with
        | none => rw [hai, hz] at hs; cases hs
        | some ts' =>
          rw [hai, hz] at hs
          simp only [Option.some.injEq] at hs
          subst hs
          obtain ⟨h1, h3, h4, h5⟩ := setst_inv (st' := ts') hai hI.tc hI.niq hI.cnt hI.inq
          exact ⟨h1, hI.qc, h3, h4, h5⟩
    · rw [if_neg hcu] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`enqueue0_spec` keeps the invariants.** -/
theorem enqueue0_keeps {n i : Nat} {a a' : AData} (hs : enqueue0_spec np nc n i a = some a')
    (hI : AInv np nc a) : AInv np nc a' := by
  unfold enqueue0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n ≤ nc ∧ i < np
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn, hi⟩ := hc
    cases hl : a.abq n with
    | AbQUndef => rw [hl] at hs; cases hs
    | AbQValid l =>
      rw [hl] at hs
      simp only at hs
      by_cases hcu : (a.AC i).cused = true
      · rw [if_pos hcu] at hs
        cases hai : a.abtcb i with
        | AbTCBUndef => rw [hai] at hs; cases hs
        | AbTCBValid st b =>
          rw [hai] at hs
          simp only at hs
          by_cases hb : b = -1
          · rw [if_pos hb] at hs
            simp only [Option.some.injEq] at hs
            subst hs; subst hb
            obtain ⟨h1, h2, h3, h4, h5⟩ := enq_inv hn hi hl hai hcu hI.tc hI.qc hI.niq hI.cnt hI.inq
            exact ⟨h1, h2, h3, h4, h5⟩
          · rw [if_neg hb] at hs; cases hs
      · rw [if_neg hcu] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`dequeue0_spec` keeps the invariants.** -/
theorem dequeue0_keeps {n r : Nat} {a a' : AData} (hs : dequeue0_spec np nc n a = some (a', r))
    (hI : AInv np nc a) : AInv np nc a' ∧ r ≤ np := by
  unfold dequeue0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n ≤ nc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    cases hl : a.abq n with
    | AbQUndef => rw [hl] at hs; cases hs
    | AbQValid l =>
      rw [hl] at hs
      simp only at hs
      by_cases hla : l.getLastD np = np
      · rw [if_pos hla] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨ha', hr⟩ := hs
        subst ha'; subst hr
        exact ⟨hI, by omega⟩
      · rw [if_neg hla] at hs
        have hmem : l.getLastD np ∈ l := by
          rcases List.eq_nil_or_concat l with e | ⟨r0, la, e⟩
          · subst e; exact absurd rfl hla
          · rw [List.concat_eq_append] at e
            subst e
            rw [List.getLastD_concat]
            exact List.mem_append_right _ List.mem_cons_self
        have hlt := q_lt hI.qc hn hl hmem
        cases hai : a.abtcb (l.getLastD np) with
        | AbTCBUndef => rw [hai] at hs; cases hs
        | AbTCBValid st b =>
          rw [hai] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨ha', hr⟩ := hs
          subst ha'; subst hr
          obtain ⟨s, hs'⟩ := hI.inq _ n l hlt hn hl hmem
          rw [hai] at hs'
          injection hs' with e1 e2
          subst e2
          obtain ⟨h1, h2, h3, h4, h5⟩ := rmv_inv hn hlt hl hai hI.tc hI.qc hI.niq hI.cnt hI.inq
          exact ⟨⟨h1, h2, h3, h4, h5⟩, by omega⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`queue_rmv0_spec` keeps the invariants.** -/
theorem queue_rmv0_keeps {n i : Nat} {a a' : AData} (hs : queue_rmv0_spec np nc n i a = some a')
    (hI : AInv np nc a) : AInv np nc a' := by
  unfold queue_rmv0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n ≤ nc ∧ i < np
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn, hi⟩ := hc
    cases hl : a.abq n with
    | AbQUndef => rw [hl] at hs; cases hs
    | AbQValid l =>
      cases hai : a.abtcb i with
      | AbTCBUndef => rw [hl, hai] at hs; cases hs
      | AbTCBValid st b =>
        rw [hl, hai] at hs
        simp only at hs
        by_cases hb : (n : Int) = b
        · rw [if_pos hb] at hs
          simp only [Option.some.injEq] at hs
          subst hs; subst hb
          obtain ⟨h1, h2, h3, h4, h5⟩ := rmv_inv hn hi hl hai hI.tc hI.qc hI.niq hI.cnt hI.inq
          exact ⟨h1, h2, h3, h4, h5⟩
        · rw [if_neg hb] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

end Keeps

/-! ## The region, seen as lists -/

/-- The list view `a` of the pointer state `q`: the rest of the state is
the same, the threads and queues are related, and `q` satisfies the
invariants of its own layer. -/
def RelA (np nc : Nat) (a : AData) (q : QData) : Prop :=
  a.toSData = q.toSData ∧ AbQ_RealQ np nc a.abtcb a.abq q.tcb q.tdq ∧ TCBCorrect_range np q.tcb ∧
    TDQCorrect_range np nc q.tdq

/-- The region matches the list view. -/
def MatchA (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb : Nat) (a : AData) (b : Region) : Prop :=
  ∃ q : QData, MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb q b ∧
    RelA num_proc num_chan a q

/-- `set_state_spec` keeps the pointer view's invariant. -/
theorem set_state_keeps {np n s : Nat} {t t' : TData} (hs : set_state_spec np n s t = some t')
    (hT : TCBCorrect_range np t.tcb) : TCBCorrect_range np t'.tcb := by
  unfold set_state_spec at hs
  by_cases hc : t.pg = true ∧ t.ipt = true ∧ n < np
  · rw [if_pos hc] at hs
    cases ht : t.tcb n with
    | TCBUndef => rw [ht] at hs; cases hs
    | TCBValid ts p nx =>
      cases hz : ZtoThreadState s with
      | none => rw [ht, hz] at hs; cases hs
      | some ts' =>
        rw [ht, hz] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨hp, hnx⟩ := tcbc_get hT hc.2.2 ht
        exact tcbc_set hT n hp hnx
  · rw [if_neg hc] at hs; cases hs

/-- **The initial states are related**: `real_tcb`, `real_tdq` are the
pointer view of `real_abtcb`, `real_abq`. -/
theorem real_relA {np nc : Nat} {a : AData} {q : QData} (hS : a.toSData = q.toSData) :
    RelA np nc { a with abtcb := real_abtcb np a.abtcb, abq := real_abq nc a.abq }
      { q with tcb := real_tcb np q.tcb, tdq := real_tdq np nc q.tdq } :=
  ⟨hS, real_data _ _ _ _, real_tcb_correct _, real_tdq_correct _⟩

section Triples
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MQ" => MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb
local notation "MA" => MatchA maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb

/-- `get_state` in the state with the queues. -/
theorem getStateQ_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 MQ (fun _ => False)
      (fun σ q => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_state_spec num_proc n q.toTData = some v)
      (getTStateS tb x ie)
      (fun σ q σ' q' => q' = q ∧ ∃ v, get_state_spec num_proc n q.toTData = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ q ⟨he, v, hs⟩ => ?_)
  have hs0 := hs
  unfold get_state_spec at hs
  by_cases hc : q.toTData.pg = true ∧ q.toTData.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    cases ht : q.toTData.tcb n with
    | TCBUndef => rw [ht] at hs; cases hs
    | TCBValid ts p nx =>
      rw [ht] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, q, getTStateQ εR c i0 hL x hx he hc.2.2 ht, rfl, _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- `set_state` in the state with the queues. -/
theorem setStateQ_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (ie ve : Expr)
    (n sv : Nat) :
    Triple εR c i0 MQ (TF tb num_proc)
      (fun σ q => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ t1, set_state_spec num_proc n sv q.toTData = some t1)
      (setTStateS tb ie ve)
      (fun σ q σ' q' => ∃ t1, set_state_spec num_proc n sv q.toTData = some t1 ∧
        q' = { q with toTData := t1 } ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ q ⟨he, hve, t1, hs⟩ => ?_)
  have hs0 := hs
  unfold set_state_spec at hs
  by_cases hc : q.toTData.pg = true ∧ q.toTData.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    cases ht : q.toTData.tcb n with
    | TCBUndef => rw [ht] at hs; cases hs
    | TCBValid ts p nx =>
      cases hz : ZtoThreadState sv with
      | none => rw [ht, hz] at hs; cases hs
      | some ts' =>
        rw [ht, hz] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨_, _, setTStateQ εR c i0 hL (fun _ h => h) he hve hc.2.2 hz ht, _, hs0, rfl, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`get_state` refines `get_state0_spec`.** -/
theorem getState0_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 MA (fun _ => False)
      (fun σ a => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_state0_spec num_proc n a = some v)
      (getTStateS tb x ie)
      (fun σ a σ' a' => a' = a ∧ ∃ v, get_state0_spec num_proc n a = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) :=
  (getStateQ_triple εR c i0 hL x hx ie n).sim (fun σ a q hRel ⟨he, v, hs⟩ => by
    have hq := get_state_exists hRel.1 hRel.2.1 hs
    refine ⟨⟨he, v, hq⟩, fun σ' q' ⟨e, v', hv', hσ'⟩ => ?_⟩
    subst e
    rw [hq] at hv'
    injection hv' with e
    subst e
    exact ⟨a, hRel, rfl, v, hs, hσ'⟩)

/-- **`set_state` refines `set_state0_spec`.** -/
theorem setState0_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (ie ve : Expr)
    (nid n sv : Nat) (hid : nid ≤ num_proc) :
    Triple εR c i0 MA (TF tb num_proc)
      (fun σ a => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ a1, set_state0_spec nid n sv a = some a1)
      (setTStateS tb ie ve)
      (fun σ a σ' a' => set_state0_spec nid n sv a = some a' ∧ σ' = σ.set "_" 0) :=
  (setStateQ_triple εR c i0 hL ie ve n sv).sim (fun σ a q ⟨hS, hR, hT, hQ⟩ ⟨he, hve, a1, hs⟩ => by
    obtain ⟨t', ht', hS', hR'⟩ := set_state_exists hid hS hR hs
    refine ⟨⟨he, hve, t', ht'⟩, fun σ' q' ⟨t1, ht1, hq', hσ'⟩ => ?_⟩
    rw [ht'] at ht1
    injection ht1 with e
    subst e; subst hq'
    exact ⟨a1, ⟨hS', hR', set_state_keeps ht' hT, hQ⟩, hs, hσ'⟩)

/-- **`enqueue` refines `enqueue0_spec`.** -/
theorem enqueue0_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (n i : Nat) :
    Triple εR c i0 MA (QTF tb num_proc qb num_chan)
      (fun σ a => σ "chan_index" = BitVec.ofNat 32 n ∧ σ "proc_index" = BitVec.ofNat 32 i ∧
        AInv num_proc num_chan a ∧ ∃ a1, enqueue0_spec num_proc num_chan n i a = some a1)
      (enqueueS tb qb num_proc)
      (fun _ a _ a' => enqueue0_spec num_proc num_chan n i a = some a') :=
  (enqueue_triple εR c i0 hL n i).sim (fun σ a q ⟨hS, hR, hT, hQ⟩ ⟨hcn, hpi, hI, a1, hs⟩ => by
    obtain ⟨q', hq', hS', hR'⟩ := enqueue_exists hS hR hI.qc hI.cnt hI.inq hs
    refine ⟨⟨hcn, hpi, q', hq'⟩, fun σ' d' hd' => ?_⟩
    rw [hq'] at hd'
    injection hd' with e
    subst e
    obtain ⟨hT', hQ'⟩ := enqueue_keeps hq' hT hQ
    exact ⟨a1, ⟨hS', hR', hT', hQ'⟩, hs⟩)

/-- **`dequeue` refines `dequeue0_spec`.** -/
theorem dequeue0_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (n : Nat) :
    Triple εR c i0 MA (QTF tb num_proc qb num_chan)
      (fun σ a => σ "chan_index" = BitVec.ofNat 32 n ∧ AInv num_proc num_chan a ∧
        ∃ a1 r, dequeue0_spec num_proc num_chan n a = some (a1, r))
      (dequeueS tb qb num_proc)
      (fun _ a σ' a' => ∃ r, dequeue0_spec num_proc num_chan n a = some (a', r) ∧
        σ' "proc_index" = BitVec.ofNat 32 r) :=
  (dequeue_triple εR c i0 hL n).sim (fun σ a q ⟨hS, hR, hT, hQ⟩ ⟨hcn, hI, a1, r, hs⟩ => by
    obtain ⟨q', hq', hS', hR'⟩ := dequeue_exists hS hR hI.qc hI.cnt hI.inq hs
    refine ⟨⟨hcn, hT, q', r, hq'⟩, fun σ' d' ⟨r', hd', hr'⟩ => ?_⟩
    rw [hq'] at hd'
    injection hd' with e
    injection e with e1 e2
    subst e1; subst e2
    obtain ⟨hT', hQ', -⟩ := dequeue_keeps hq' hT hQ
    exact ⟨a1, ⟨hS', hR', hT', hQ'⟩, r, hs, hr'⟩)

/-- **`queue_rmv` refines `queue_rmv0_spec`.** -/
theorem queueRmv0_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (n i : Nat) :
    Triple εR c i0 MA (QTF tb num_proc qb num_chan)
      (fun σ a => σ "chan_index" = BitVec.ofNat 32 n ∧ σ "proc_index" = BitVec.ofNat 32 i ∧
        AInv num_proc num_chan a ∧ ∃ a1, queue_rmv0_spec num_proc num_chan n i a = some a1)
      (queueRmvS tb qb num_proc)
      (fun _ a _ a' => queue_rmv0_spec num_proc num_chan n i a = some a') :=
  (queueRmv_triple εR c i0 hL n i).sim (fun σ a q ⟨hS, hR, hT, hQ⟩ ⟨hcn, hpi, hI, a1, hs⟩ => by
    obtain ⟨q', hq', hS', hR'⟩ := queue_rmv_exists hS hR hI.qc hI.cnt hI.inq hs
    refine ⟨⟨hcn, hpi, hT, q', hq'⟩, fun σ' d' hd' => ?_⟩
    rw [hq'] at hd'
    injection hd' with e
    subst e
    obtain ⟨hT', hQ'⟩ := queueRmv_keeps hq' hT hQ
    exact ⟨a1, ⟨hS', hR', hT', hQ'⟩, hs⟩)

end Triples

end PAbQueue
