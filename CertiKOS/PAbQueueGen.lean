import CertiKOS.PAbQueue

/-!
# mCertiKOS `AbQueueGen`: the list operations are the pointer operations

The refinement between `PAbQueue` (queues as lists) and `PQueueInit` (linked
control blocks), ported from `proc/AbQueueGen.v`.

* `get_state_exists`, `set_state_exists`, `enqueue_exists`, `dequeue_exists`,
  `queue_rmv_exists`: when an operation on lists succeeds, the operation on
  pointers succeeds from every related state, with the same result, and the
  states it reaches are related.
* `RelA`, `MatchA`: the relation, and the region seen as lists.
* `getState0_triple` … `queueRmv0_triple`: **the C code of the layer below
  refines the list specifications** (`Triple.sim`).
* `tdqueueInit0_rel`: initialisation gives related states.

As in mCertiKOS the proofs use the invariants of the list view:
`AbQCorrect_range`, `QCount` and `InQ`. They make a queue's list free of
repeats and the queues disjoint, so a control block that changes is seen by
one list only.

What differs: `RelA` also carries the invariants of the pointer view
(`TCBCorrect_range`, `TDQCorrect_range`). mCertiKOS keeps them as the lower
layer's own invariant; `dequeue` and `queue_rmv` need them.
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

section Sim
variable {np nc : Nat}

/-- The flags are the same in both views. -/
theorem flags_eq {a : AData} {q : QData} (hS : a.toSData = q.toSData) : q.pg = a.pg ∧ q.ipt = a.ipt := by
  constructor
  · show q.toSData.pg = a.toSData.pg
    rw [hS]
  · show q.toSData.ipt = a.toSData.ipt
    rw [hS]

/-- `get_state_exists`. -/
theorem get_state_exists {a : AData} {q : QData} {n v : Nat} (hS : a.toSData = q.toSData)
    (hR : AbQ_RealQ np nc a.abtcb a.abq q.tcb q.tdq) (hs : get_state0_spec np n a = some v) :
    get_state_spec np n q.toTData = some v := by
  obtain ⟨epg, eipt⟩ := flags_eq hS
  unfold get_state0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n < np
  · rw [if_pos hc] at hs
    cases hai : a.abtcb n with
    | AbTCBUndef => rw [hai] at hs; cases hs
    | AbTCBValid s b =>
      rw [hai] at hs
      simp only [Option.some.injEq] at hs
      obtain ⟨pv, nx, ht⟩ := hR.tp n s b hc.2.2 hai
      have ht' : q.toTData.tcb n = .TCBValid s pv nx := ht
      unfold get_state_spec
      rw [if_pos ⟨epg.trans hc.1, eipt.trans hc.2.1, hc.2.2⟩, ht']
      simp only
      rw [hs]
  · rw [if_neg hc] at hs; cases hs

/-- `set_state_exists`. The list view bounds the thread by `num_id`, the
pointer view by `num_proc`; they are one constant in mCertiKOS. -/
theorem set_state_exists {a a' : AData} {q : QData} {num_id n s : Nat} (hid : num_id ≤ np)
    (hS : a.toSData = q.toSData) (hR : AbQ_RealQ np nc a.abtcb a.abq q.tcb q.tdq)
    (hs : set_state0_spec num_id n s a = some a') :
    ∃ t', set_state_spec np n s q.toTData = some t' ∧ a'.toSData = t'.toSData ∧
      AbQ_RealQ np nc a'.abtcb a'.abq t'.tcb q.tdq := by
  obtain ⟨epg, eipt⟩ := flags_eq hS
  unfold set_state0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n < num_id
  · rw [if_pos hc] at hs
    obtain ⟨hpg, hipt, hn⟩ := hc
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
          obtain ⟨pv, nx, ht⟩ := hR.tp n st b (by omega) hai
          have ht' : q.toTData.tcb n = .TCBValid st pv nx := ht
          refine ⟨{ q.toTData with tcb := setAt q.tcb n (.TCBValid ts' pv nx) }, ?_, hS, ?_, ?_⟩
          · unfold set_state_spec
            rw [if_pos ⟨epg.trans hpg, eipt.trans hipt, by omega⟩, ht', hz]
          · intro qi l hqi hl
            obtain ⟨hd, tl, h1, h2⟩ := hR.dl qi l hqi hl
            refine ⟨hd, tl, h1, (rec_iff np _ np hd l tl np).2 ?_⟩
            obtain ⟨d1, d2, d3⟩ := (rec_iff np q.tcb np hd l tl np).1 h2
            refine ⟨d1, d2, fun x p nx' hm => ?_⟩
            obtain ⟨st0, h0⟩ := d3 x p nx' hm
            by_cases e : x = n
            · subst e
              rw [ht] at h0
              injection h0 with e1 e2 e3
              subst e2; subst e3
              exact ⟨ts', setAt_eq _ _ _⟩
            · exact ⟨st0, by show setAt q.tcb n _ x = _; rw [setAt_ne _ _ e]; exact h0⟩
          · intro i tds inq hi he
            by_cases e : i = n
            · subst e
              have he' : setAt a.abtcb i (.AbTCBValid ts' b) i = .AbTCBValid tds inq := he
              rw [setAt_eq] at he'
              injection he' with e1 e2
              subst e1
              exact ⟨pv, nx, setAt_eq _ _ _⟩
            · have he' : setAt a.abtcb n (.AbTCBValid ts' b) i = .AbTCBValid tds inq := he
              rw [setAt_ne _ _ e] at he'
              obtain ⟨pv', nx', h'⟩ := hR.tp i tds inq hi he'
              exact ⟨pv', nx', by show setAt q.tcb n _ i = _; rw [setAt_ne _ _ e]; exact h'⟩
    · rw [if_neg hcu] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`enqueue_exists`.** -/
theorem enqueue_exists {a a' : AData} {q : QData} {n i : Nat} (hS : a.toSData = q.toSData)
    (hR : AbQ_RealQ np nc a.abtcb a.abq q.tcb q.tdq) (hQC : AbQCorrect_range np nc a.abq)
    (hCnt : QCount np nc a.abtcb a.abq) (hIn : InQ np nc a.abtcb a.abq)
    (hs : enqueue0_spec np nc n i a = some a') :
    ∃ q', enqueue_spec np nc n i q = some q' ∧ a'.toSData = q'.toSData ∧
      AbQ_RealQ np nc a'.abtcb a'.abq q'.tcb q'.tdq := by
  obtain ⟨epg, eipt⟩ := flags_eq hS
  unfold enqueue0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n ≤ nc ∧ i < np
  · rw [if_pos hc] at hs
    obtain ⟨hpg, hipt, hn, hi⟩ := hc
    have hpg' : q.pg = true := epg.trans hpg
    have hipt' : q.ipt = true := eipt.trans hipt
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
            obtain ⟨hd, tl, hq, hrec⟩ := hR.dl n l hn hl
            have hdl : DL np q.tcb l hd tl := (rec_iff np q.tcb np hd l tl np).1 hrec
            obtain ⟨pv, nx, hti⟩ := hR.tp i st (-1) hi hai
            have hnot : ∀ qi l', qi ≤ nc → a.abq qi = .AbQValid l' → i ∉ l' := by
              intro qi l' hqi hl' hmem
              obtain ⟨s, hs'⟩ := hIn i qi l' hi hqi hl' hmem
              rw [hai] at hs'
              injection hs' with e1 e2
              omega
            cases l with
            | nil =>
              obtain ⟨htl, hdl'⟩ := dl_enq_nil hdl i st
              exact ⟨_, enqueue_spec_nil hpg' hipt' hn hi hq hti htl, hS,
                realQ_update hR (setAt_eq _ _ _) (fun qi e => setAt_ne _ _ e) hdl'
                  (fun qi l' x hqi e hl' hx => setAt_ne _ _ (fun e' => hnot qi l' hqi hl' (e' ▸ hx)))
                  (tp_update hR.tp (sameA_set hai _) ((SameSt.refl _).set hti _ _))⟩
            | cons t r =>
              have hnd := q_nodup hQC hCnt hIn hn hl
              obtain ⟨htl, st', htt, hdl'⟩ := dl_enq_cons hdl (hnot n _ hn hl) hnd
              have htlt : t < np := q_lt hQC hn hl List.mem_cons_self
              subst htl
              refine ⟨_, enqueue_spec_cons hpg' hipt' hn hi hq hti htlt htt, hS,
                realQ_update hR (setAt_eq _ _ _) (fun qi e => setAt_ne _ _ e) (hdl' st) ?_
                  (tp_update hR.tp (sameA_set hai _) (((SameSt.refl _).set htt _ _).set hti _ _))⟩
              intro qi l' x hqi e hl' hx
              have hxi : x ≠ i := fun e' => hnot qi l' hqi hl' (e' ▸ hx)
              have hxt : x ≠ tl := fun e' =>
                q_disjoint hQC hIn hn hqi e hl hl' List.mem_cons_self (e' ▸ hx)
              exact (setAt_ne _ _ hxi).trans (setAt_ne _ _ hxt)
          · rw [if_neg hb] at hs; cases hs
      · rw [if_neg hcu] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`dequeue_exists`.** -/
theorem dequeue_exists {a a' : AData} {q : QData} {n r : Nat} (hS : a.toSData = q.toSData)
    (hR : AbQ_RealQ np nc a.abtcb a.abq q.tcb q.tdq) (hQC : AbQCorrect_range np nc a.abq)
    (hCnt : QCount np nc a.abtcb a.abq) (hIn : InQ np nc a.abtcb a.abq)
    (hs : dequeue0_spec np nc n a = some (a', r)) :
    ∃ q', dequeue_spec np nc n q = some (q', r) ∧ a'.toSData = q'.toSData ∧
      AbQ_RealQ np nc a'.abtcb a'.abq q'.tcb q'.tdq := by
  obtain ⟨epg, eipt⟩ := flags_eq hS
  unfold dequeue0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n ≤ nc
  · rw [if_pos hc] at hs
    obtain ⟨hpg, hipt, hn⟩ := hc
    have hpg' : q.pg = true := epg.trans hpg
    have hipt' : q.ipt = true := eipt.trans hipt
    cases hl : a.abq n with
    | AbQUndef => rw [hl] at hs; cases hs
    | AbQValid l =>
      rw [hl] at hs
      simp only at hs
      obtain ⟨hd, tl, hq, hrec⟩ := hR.dl n l hn hl
      have hdl : DL np q.tcb l hd tl := (rec_iff np q.tcb np hd l tl np).1 hrec
      by_cases hla : l.getLastD np = np
      · rw [if_pos hla] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨ha', hr⟩ := hs
        subst ha'; subst hr
        refine ⟨q, ?_, hS, hR⟩
        rw [hla]
        exact dequeue_spec_empty hpg' hipt' hn hq (hdl.1.trans hla)
      · rw [if_neg hla] at hs
        rcases List.eq_nil_or_concat l with e | ⟨r0, la, e⟩
        · subst e; exact absurd rfl hla
        · rw [List.concat_eq_append] at e
          subst e
          simp only [List.getLastD_concat] at hs
          cases hai : a.abtcb la with
          | AbTCBUndef => rw [hai] at hs; cases hs
          | AbTCBValid st b =>
            rw [hai] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨ha', hr⟩ := hs
            subst ha'; subst hr
            have hnd := q_nodup hQC hCnt hIn hn hl
            have hlalt : la < np := q_lt hQC hn hl (List.mem_append_right _ List.mem_cons_self)
            obtain ⟨hhd, stc, hth⟩ := dl_last hdl
            have hhd' := hhd.symm
            subst hhd'
            have hlar : la ∉ r0 := fun h =>
              (List.nodup_append.1 hnd).2.2 la h la List.mem_cons_self rfl
            have hrm : remove la (r0 ++ [la]) = r0 := by
              have := remove_mid hlar (List.not_mem_nil (a := la))
              rwa [List.append_nil] at this
            rw [hrm]
            rcases List.eq_nil_or_concat r0 with e | ⟨r', x, e⟩
            · subst e
              exact ⟨_, dequeue_spec_one hpg' hipt' hn hq hlalt hth rfl, hS,
                realQ_update hR (setAt_eq _ _ _) (fun qi e => setAt_ne _ _ e) (dl_nil q.tcb)
                  (fun _ _ _ _ _ _ _ => rfl) (tp_update hR.tp (sameA_set hai _) (SameSt.refl _))⟩
            · rw [List.concat_eq_append] at e
              subst e
              obtain ⟨st', htx, hdl'⟩ := dl_deq_more hdl hnd
              have hxm : x ∈ r' ++ [x] ++ [la] :=
                List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
              have hxlt : x < np := q_lt hQC hn hl hxm
              rw [List.getLastD_concat] at hth
              refine ⟨_, dequeue_spec_more hpg' hipt' hn hq hlalt hth (Nat.ne_of_lt hxlt) htx, hS,
                realQ_update hR (setAt_eq _ _ _) (fun qi e => setAt_ne _ _ e) hdl' ?_
                  (tp_update hR.tp (sameA_set hai _) ((SameSt.refl _).set htx _ _))⟩
              intro qi l' y hqi e hl' hy
              exact setAt_ne _ _ (fun e' => q_disjoint hQC hIn hn hqi e hl hl' hxm (e' ▸ hy))
  · rw [if_neg hc] at hs; cases hs

/-- **`queue_rmv_exists`.** -/
theorem queue_rmv_exists {a a' : AData} {q : QData} {n i : Nat} (hS : a.toSData = q.toSData)
    (hR : AbQ_RealQ np nc a.abtcb a.abq q.tcb q.tdq) (hQC : AbQCorrect_range np nc a.abq)
    (hCnt : QCount np nc a.abtcb a.abq) (hIn : InQ np nc a.abtcb a.abq)
    (hs : queue_rmv0_spec np nc n i a = some a') :
    ∃ q', queue_rmv_spec np nc n i q = some q' ∧ a'.toSData = q'.toSData ∧
      AbQ_RealQ np nc a'.abtcb a'.abq q'.tcb q'.tdq := by
  obtain ⟨epg, eipt⟩ := flags_eq hS
  unfold queue_rmv0_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n ≤ nc ∧ i < np
  · rw [if_pos hc] at hs
    obtain ⟨hpg, hipt, hn, hi⟩ := hc
    have hpg' : q.pg = true := epg.trans hpg
    have hipt' : q.ipt = true := eipt.trans hipt
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
          obtain ⟨hd, tl, hq, hrec⟩ := hR.dl n l hn hl
          have hdl : DL np q.tcb l hd tl := (rec_iff np q.tcb np hd l tl np).1 hrec
          have hnd := q_nodup hQC hCnt hIn hn hl
          obtain ⟨l0, hl0, hcnt⟩ := hCnt i st n hi hai (by omega) (by omega)
          have e : ((n : Int)).toNat = n := by omega
          rw [e, hl] at hl0
          cases hl0
          have him : i ∈ l := List.count_pos_iff.1 (by omega)
          obtain ⟨l1, l2, e⟩ := List.append_of_mem him
          subst e
          obtain ⟨hn1, hn2, hn3⟩ := List.nodup_append.1 hnd
          have hi1 : i ∉ l1 := fun h => hn3 i h i List.mem_cons_self rfl
          have hi2 : i ∉ l2 := (List.nodup_cons.1 hn2).1
          rw [remove_mid hi1 hi2]
          obtain ⟨stc, hti⟩ := dl_mid hdl
          rcases List.eq_nil_or_concat l1 with e1 | ⟨l1', x, e1⟩
          · subst e1
            cases l2 with
            | nil =>
              exact ⟨_, queue_rmv_spec_A hpg' hipt' hn hi hti hq rfl rfl, hS,
                realQ_update hR (setAt_eq _ _ _) (fun qi e => setAt_ne _ _ e) (dl_nil q.tcb)
                  (fun _ _ _ _ _ _ _ => rfl) (tp_update hR.tp (sameA_set hai _) (SameSt.refl _))⟩
            | cons y l2' =>
              obtain ⟨st0, hty, hdl'⟩ := dl_rmv_tail (np := np) (tcb := q.tcb) (i := i) (y := y) (l2' := l2')
                (hd := hd) (tl := tl) hdl hnd
              have hym : y ∈ [] ++ i :: y :: l2' := List.mem_cons_of_mem _ List.mem_cons_self
              have hylt : y < np := q_lt hQC hn hl hym
              refine ⟨_, queue_rmv_spec_C hpg' hipt' hn hi hti hq (Nat.ne_of_lt hylt) hty rfl, hS,
                realQ_update hR (setAt_eq _ _ _) (fun qi e => setAt_ne _ _ e) hdl' ?_
                  (tp_update hR.tp (sameA_set hai _) ((SameSt.refl _).set hty _ _))⟩
              intro qi l' z hqi e hl' hz
              exact setAt_ne _ _ (fun (e' : z = y) => q_disjoint hQC hIn hn hqi e hl hl' hym (e' ▸ hz))
          · rw [List.concat_eq_append] at e1
            subst e1
            rw [List.getLastD_concat] at hti
            have hxm : ∀ l2, x ∈ l1' ++ [x] ++ i :: l2 := fun _ =>
              List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
            have hxlt : x < np := q_lt hQC hn hl (hxm l2)
            cases l2 with
            | nil =>
              obtain ⟨st1, htx, hdl'⟩ := dl_deq_more hdl hnd
              rw [List.append_nil]
              refine ⟨_, queue_rmv_spec_B hpg' hipt' hn hi hti hq rfl (Nat.ne_of_lt hxlt) htx, hS,
                realQ_update hR (setAt_eq _ _ _) (fun qi e => setAt_ne _ _ e) hdl' ?_
                  (tp_update hR.tp (sameA_set hai _) ((SameSt.refl _).set htx _ _))⟩
              intro qi l' z hqi e hl' hz
              exact setAt_ne _ _ (fun e' => q_disjoint hQC hIn hn hqi e hl hl' (hxm []) (e' ▸ hz))
            | cons y l2' =>
              obtain ⟨st0, st1, hty, htx, hxy, hdl'⟩ := dl_rmv_mid hdl hnd
              have hym : y ∈ l1' ++ [x] ++ i :: y :: l2' :=
                List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hylt : y < np := q_lt hQC hn hl hym
              refine ⟨_, queue_rmv_spec_D hpg' hipt' hn hi hti hq (Nat.ne_of_lt hylt) hty
                (Nat.ne_of_lt hxlt) htx, hS,
                realQ_update hR hq (fun _ _ => rfl) hdl' ?_
                  (tp_update hR.tp (sameA_set hai _) (((SameSt.refl _).set hty _ _).set htx _ _))⟩
              intro qi l' z hqi e hl' hz
              have hzx : z ≠ x := fun e' =>
                q_disjoint hQC hIn hn hqi e hl hl' (hxm (y :: l2')) (e' ▸ hz)
              have hzy : z ≠ y := fun e' => q_disjoint hQC hIn hn hqi e hl hl' hym (e' ▸ hz)
              exact (setAt_ne _ _ hzx).trans (setAt_ne _ _ hzy)
        · rw [if_neg hb] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

end Sim

end PAbQueue
