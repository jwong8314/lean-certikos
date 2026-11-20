import CertiKOS.PSchedInit

/-!
# mCertiKOS `PThreadSched`: `thread_wakeup`, ported

The scheduler functions that need no context switch. This file has
`thread_wakeup`: the thread at the head of a sleep queue becomes ready.

Ported from `objects/ObjThread.v`: `thread_wakeup_spec`. Ported from
`proc/PCurIDCSource.v`: the C code.

* `thread_wakeup_factors`: **the specification is its three calls**:
  `dequeue`, then, if a thread came out, `set_state(READY)` and `enqueue` on
  the ready queue, each by its own specification over lists. The invariants
  are used here, as in mCertiKOS's code proof: `InQ` says the thread taken
  off the queue was on it, and then `NotInQ` says it has a container, which
  `set_state` and `enqueue` require.
* `thread_wakeup_triple`: **`thread_wakeup` refines `thread_wakeup_spec`.**
  It is the first function verified on the list view alone: the proof calls
  the triples of `PAbQueue` and never mentions a control block.
* `thread_wakeup_keeps`: the specification keeps the invariants.

Not here: `thread_spawn`, `thread_sched`, `thread_yield`, `thread_sleep`,
which need kernel contexts.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PSched

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID

/-- **`thread_wakeup_spec`**: the head of queue `n` goes to the ready queue,
which is queue `num_chan`. -/
def thread_wakeup_spec (num_proc num_chan n : Nat) (d : AData) : Option AData :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_chan then
    match d.abq n with
    | .AbQUndef => none
    | .AbQValid l =>
      if l.getLastD num_proc = num_proc then some d
      else
        match d.abtcb (l.getLastD num_proc), d.abq num_chan with
        | .AbTCBValid _ _, .AbQValid l' =>
          some { d with
            abtcb := setAt d.abtcb (l.getLastD num_proc) (.AbTCBValid .READY num_chan)
            abq := setAt (setAt d.abq n (.AbQValid (remove (l.getLastD num_proc) l))) num_chan
              (.AbQValid (l.getLastD num_proc :: l')) }
        | _, _ => none
  else none

/-- ```
proc_index = dequeue(chan_index);
if (proc_index != num_proc) {
  set_state(proc_index, TSTATE_READY);
  enqueue(num_chan, proc_index);
}
``` -/
def threadWakeupS (tb qb num_proc num_chan : Nat) : Stmt APrim :=
  .seq (dequeueS tb qb num_proc)
    (.ite (.bin .ne (.var "proc_index") (.const (BitVec.ofNat 32 num_proc)))
      (.seq (setTStateS tb (.var "proc_index") (.const 0))
        (.seq (.assign "chan_index" (.const (BitVec.ofNat 32 num_chan))) (enqueueS tb qb num_proc)))
      .skip)

theorem AData.ext3 {d1 d2 : AData} (h1 : d1.toSData = d2.toSData) (h2 : d1.abtcb = d2.abtcb)
    (h3 : d1.abq = d2.abq) : d1 = d2 := by
  obtain ⟨s1, t1, q1⟩ := d1
  obtain ⟨s2, t2, q2⟩ := d2
  change s1 = s2 at h1; change t1 = t2 at h2; change q1 = q2 at h3
  subst h1; subst h2; subst h3; rfl

section Spec
variable {np nc : Nat}

/-- **`thread_wakeup_spec` is its calls.** -/
theorem thread_wakeup_factors {n : Nat} {a a' : AData} (hI : AInv np nc a)
    (hs : thread_wakeup_spec np nc n a = some a') :
    (dequeue0_spec np nc n a = some (a, np) ∧ a' = a) ∨
    ∃ a1 a2 la, la < np ∧ dequeue0_spec np nc n a = some (a1, la) ∧
      set_state0_spec np la 0 a1 = some a2 ∧ enqueue0_spec np nc nc la a2 = some a' := by
  unfold thread_wakeup_spec at hs
  by_cases hc : a.pg = true ∧ a.ipt = true ∧ n < nc
  · rw [if_pos hc] at hs
    obtain ⟨hpg, hipt, hn⟩ := hc
    have hc' : a.pg = true ∧ a.ipt = true ∧ n ≤ nc := ⟨hpg, hipt, Nat.le_of_lt hn⟩
    cases hl : a.abq n with
    | AbQUndef => rw [hl] at hs; cases hs
    | AbQValid l =>
      rw [hl] at hs
      simp only at hs
      by_cases hla : l.getLastD np = np
      · rw [if_pos hla] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        refine Or.inl ⟨?_, rfl⟩
        unfold dequeue0_spec
        rw [if_pos hc', hl]
        simp only
        rw [if_pos hla, hla]
      · rw [if_neg hla] at hs
        have hmem : l.getLastD np ∈ l := by
          rcases List.eq_nil_or_concat l with e | ⟨r0, x, e⟩
          · subst e; exact absurd rfl hla
          · rw [List.concat_eq_append] at e
            subst e
            rw [List.getLastD_concat]
            exact List.mem_append_right _ List.mem_cons_self
        have hlt := q_lt hI.qc (Nat.le_of_lt hn) hl hmem
        obtain ⟨s, hai⟩ := hI.inq _ n l hlt (Nat.le_of_lt hn) hl hmem
        generalize hg : l.getLastD np = la at hs hla hmem hlt hai
        rw [hai] at hs
        cases hq : a.abq nc with
        | AbQUndef => rw [hq] at hs; cases hs
        | AbQValid l' =>
          rw [hq] at hs
          simp only [Option.some.injEq] at hs
          have hcu : (a.AC la).cused = true := by
            cases hcb : (a.AC la).cused with
            | true => rfl
            | false =>
              have := hI.niq la s n hlt hcb hai
              omega
          have hdq : dequeue0_spec np nc n a = some ({ a with
              abtcb := setAt a.abtcb la (.AbTCBValid s (-1))
              abq := setAt a.abq n (.AbQValid (remove la l)) }, la) := by
            unfold dequeue0_spec
            rw [if_pos hc', hl]
            simp only
            rw [hg, if_neg hla, hai]
          have hss : set_state0_spec np la 0 ({ a with
                abtcb := setAt a.abtcb la (.AbTCBValid s (-1))
                abq := setAt a.abq n (.AbQValid (remove la l)) } : AData) =
              some { a with
                abtcb := setAt (setAt a.abtcb la (.AbTCBValid s (-1))) la (.AbTCBValid .READY (-1))
                abq := setAt a.abq n (.AbQValid (remove la l)) } := by
            have h1 : setAt a.abtcb la (.AbTCBValid s (-1)) la = .AbTCBValid s (-1) := setAt_eq _ _ _
            unfold set_state0_spec
            simp only
            rw [if_pos ⟨hpg, hipt, hlt⟩, if_pos hcu, h1]
            rfl
          refine Or.inr ⟨_, _, la, hlt, hdq, hss, ?_⟩
          have h2 : setAt (setAt a.abtcb la (.AbTCBValid s (-1))) la (.AbTCBValid .READY (-1)) la =
              .AbTCBValid .READY (-1) := setAt_eq _ _ _
          have h3 : setAt a.abq n (.AbQValid (remove la l)) nc = .AbQValid l' := by
            rw [setAt_ne _ _ (Nat.ne_of_gt hn)]; exact hq
          unfold enqueue0_spec
          simp only
          rw [if_pos ⟨hpg, hipt, Nat.le_refl _, hlt⟩, h3]
          simp only
          rw [if_pos hcu, h2]
          simp only
          rw [if_pos trivial, ← hs]
          exact congrArg some (AData.ext3 rfl (by
            show setAt (setAt (setAt a.abtcb la _) la _) la _ = setAt a.abtcb la _
            rw [setAt_setAt, setAt_setAt]) rfl)
  · rw [if_neg hc] at hs; cases hs

/-- **`thread_wakeup_spec` keeps the invariants.** -/
theorem thread_wakeup_keeps {n : Nat} {a a' : AData} (hI : AInv np nc a)
    (hs : thread_wakeup_spec np nc n a = some a') : AInv np nc a' := by
  rcases thread_wakeup_factors hI hs with ⟨-, rfl⟩ | ⟨a1, a2, la, -, hdq, hss, henq⟩
  · exact hI
  · exact enqueue0_keeps henq (set_state0_keeps hss (dequeue0_keeps hdq hI).1)

end Spec

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MA" => MatchA maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb

/-- **`thread_wakeup` refines `thread_wakeup_spec`.** -/
theorem thread_wakeup_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (n : Nat) :
    Triple εR c i0 MA (QTF tb num_proc qb num_chan)
      (fun σ a => σ "chan_index" = BitVec.ofNat 32 n ∧ AInv num_proc num_chan a ∧
        ∃ a1, thread_wakeup_spec num_proc num_chan n a = some a1)
      (threadWakeupS tb qb num_proc num_chan)
      (fun _ a _ a' => thread_wakeup_spec num_proc num_chan n a = some a') := by
  rintro σ l b a hlk hcs hM ⟨hcn, hI, a', hs⟩
  have hnp : num_proc < 2 ^ 32 := np_lt hL
  rcases thread_wakeup_factors hI hs with ⟨hdq, e0⟩ | ⟨a1, a2, la, hlt, hdq, hss, henq⟩
  · subst e0
    obtain ⟨σ1, l1, b1, a1', hr1, hcs1, hM1, hlk1, hf1, r, hq1, hpi⟩ :=
      dequeue0_triple εR c i0 hL n σ l b a' hlk hcs hM ⟨hcn, hI, _, _, hdq⟩
    rw [hdq] at hq1
    injection hq1 with e
    injection e with e1 e2
    subst e1; subst e2
    exact ⟨σ1, l1, b1, a', Runs.seq hr1 (Runs.ite_false (nec_false hpi rfl) Runs.skip), hcs1, hM1, hlk1,
      hf1, hs⟩
  · obtain ⟨σ1, l1, b1, a1', hr1, hcs1, hM1, hlk1, hf1, r, hq1, hpi⟩ :=
      dequeue0_triple εR c i0 hL n σ l b a hlk hcs hM ⟨hcn, hI, _, _, hdq⟩
    rw [hdq] at hq1
    injection hq1 with e
    injection e with e1 e2
    subst e1; subst e2
    have hI1 := (dequeue0_keeps hdq hI).1
    have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
    obtain ⟨σ2, l2, b2, a2', hr2, hcs2, hM2, hlk2, hf2, hq2, hσ2⟩ :=
      setState0_triple εR c i0 hL (.var "proc_index") (.const 0) num_proc la 0 (Nat.le_refl _) σ1 l1 b1 a1
        hlk1' hcs1 hM1 ⟨hpi, rfl, _, hss⟩
    rw [hss] at hq2
    injection hq2 with e
    subst e
    have hI2 := set_state0_keeps hss hI1
    obtain ⟨σ4, l4, b4, a4, hr4, hcs4, hM4, hlk4, hf4, hq4⟩ :=
      enqueue0_triple εR c i0 hL num_chan la (σ2.set "chan_index" (BitVec.ofNat 32 num_chan)) l2 b2 a2
        (by rw [hσ2]; simpa [Locals.set] using hlk1') hcs2 hM2
        ⟨by simp [Locals.set], by rw [hσ2]; simp [Locals.set, hpi], hI2, _, henq⟩
    rw [henq] at hq4
    injection hq4 with e
    subst e
    refine ⟨σ4, l4, b4, a', Runs.seq hr1 (Runs.ite_true
      (nec_true hpi (by omega) hnp (Nat.ne_of_lt hlt))
      (Runs.seq hr2 (Runs.seq (Runs.assign _ _) hr4))), hcs4, hM4, ?_, fun k hk => ?_, hs⟩
    · rw [hlk4, hσ2]; simp [Locals.set, hlk1]
    · rw [hf4 k hk, hf2 k (fun h => hk (Or.inl h)), hf1 k hk]

end Code

end PSched
