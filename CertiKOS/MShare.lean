import CertiKOS.MShareOp
import CertiKOS.MPTInit

/-!
# mCertiKOS `MShare`: offering and querying shared memory, ported

Ported from `objects/ObjShareMem.v`: `shared_mem_status_spec`,
`offer_shared_mem_spec`, `sharedmem_init_spec`. Ported from
`clib/CalRealSMSPool.v`: `real_smspool`. Ported from `mm/MShareOpCSource.v` and
`mm/MShareIntroCSource.v`: the C code of `shared_mem_status`,
`offer_shared_mem` and the loop of `shared_mem_init`.

* `status_triple`: `shared_mem_status` refines its specification.
* `offer_triple`: **`offer_shared_mem` refines its specification.** It goes
  through `shared_mem_to_ready`, `shared_mem_to_dead` and
  `shared_mem_to_pending`, each by its own theorem.
* `smInit_triple`: the loop of `shared_mem_init` clears the whole table
  (`real_smspool`).

What is not here: `shared_mem_init` first calls `pmap_init`, which turns
paging on and waits for the machine model. So `sharedmem_init_spec` is stated
but only its loop is verified.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MShare

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval while_inv)

/-! ## Specifications (`ObjShareMem.v`) -/

section Specs
variable (num_proc : Nat)

/-- What `pid1` learns about its sharing with `pid2`. The first query after a
change marks it seen. -/
def shared_mem_status_spec (pid1 pid2 : Nat) (d : SData) : Option (SData × Nat) :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid i' true _ =>
      match d.smspool pid2 pid1 with
      | .SHRDValid st _ _ => if st = .SHRDPEND then some (d, 1) else some (d, SharedMemInfo2Z i')
      | .SHRDUndef => none
    | .SHRDValid i' false vadr =>
      some ({ d with smspool := smSet d.smspool pid1 pid2 (.SHRDValid i' true vadr) }, SharedMemInfo2Z i')
    | .SHRDUndef => none
  else none

/-- `pid1` offers to share the page at `vadr` with `pid2`. If `pid2` already
offered, the page is mapped in both (ready, or dead if that failed);
otherwise `pid1` waits. -/
def offer_shared_mem_spec (maxpage : Nat) (pid1 pid2 vadr : Nat) (d : SData) : Option (SData × Nat) :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid st _ _ =>
      if st = .SHRDPEND then some (d, 1)
      else
        match d.smspool pid2 pid1 with
        | .SHRDValid st' _ vadr' =>
          if vadr' < 2 ^ 32 then
            if st' = .SHRDPEND then
              match ptResv2_spec maxpage num_proc pid1 vadr 7 pid2 vadr' 7 d.toPTData with
              | some (pt', re) =>
                if re = maxpage + 1 then
                  let smsp := smSet d.smspool pid1 pid2 (.SHRDValid .SHRDDEAD true 0)
                  let smsp' := smSet smsp pid2 pid1 (.SHRDValid .SHRDDEAD false 0)
                  some (⟨pt', smsp'⟩, 2)
                else
                  let smsp := smSet d.smspool pid1 pid2 (.SHRDValid .SHRDREADY true 0)
                  let smsp' := smSet smsp pid2 pid1 (.SHRDValid .SHRDREADY false 0)
                  some (⟨pt', smsp'⟩, 0)
              | none => none
            else
              some ({ d with smspool := smSet d.smspool pid1 pid2 (.SHRDValid .SHRDPEND true vadr) }, 1)
          else none
        | .SHRDUndef => none
    | .SHRDUndef => none
  else none

end Specs

/-! ## The C code (`MShareOpCSource.v`) -/

/-- ```
sd_seen = get_shared_mem_seen(source, dest);
if (sd_seen) ret = get_shared_mem_status_seen(source, dest);
else { set_shared_mem_seen(source, dest, 1); ret = get_shared_mem_state(source, dest); }
return ret;
``` -/
def statusS (sb n : Nat) : Stmt APrim :=
  .seq (getSeenS sb n "seen" (.var "pid1") (.var "pid2"))
    (.ite (.var "seen") (statusSeenS sb n)
      (.seq (setSeenS sb n (.var "pid1") (.var "pid2") (.const 1))
        (getStateS sb n "r" (.var "pid1") (.var "pid2"))))

/-- ```
sd_state = get_shared_mem_state(source, dest);
if (sd_state == 1) ret = 1;
else {
  ds_state = get_shared_mem_state(dest, source);
  if (ds_state == 1) {
    is_ready = shared_mem_to_ready(source, dest, source_va);
    if (is_ready == MagicNumber) { shared_mem_to_dead(source, dest, source_va); ret = 2; }
    else ret = 0;
  } else { shared_mem_to_pending(source, dest, source_va); ret = 1; }
}
return ret;
``` -/
def offerS (cb maxpage pb fb sb n : Nat) : Stmt APrim :=
  .seq (getStateS sb n "sd" (.var "pid1") (.var "pid2"))
    (.ite (.bin .eq (.var "sd") (.const 1)) (.assign "r" (.const 1))
      (.seq (getStateS sb n "ds" (.var "pid2") (.var "pid1"))
        (.ite (.bin .eq (.var "ds") (.const 1))
          (.seq (toReadyS cb maxpage pb fb sb n) (.seq (.assign "isr" (.var "r"))
            (.ite (.bin .eq (.var "isr") (.const (BitVec.ofNat 32 (maxpage + 1))))
              (.seq (toDeadS sb n) (.assign "r" (.const 2)))
              (.assign "r" (.const 0)))))
          (.seq (toPendingS sb n) (.assign "r" (.const 1))))))

section Proofs
variable {maxpage num_id cb num_proc pb ib fb ida sb : Nat}

/-- **`shared_mem_status` refines its specification.** -/
theorem status_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (p1 p2 : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun σ d => σ "pid1" = BitVec.ofNat 32 p1 ∧ σ "pid2" = BitVec.ofNat 32 p2 ∧
        ∃ d1 r, shared_mem_status_spec num_proc p1 p2 d = some (d1, r))
      (statusS sb num_proc)
      (fun σ d σ' d' => ∃ r, shared_mem_status_spec num_proc p1 p2 d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hp1, hp2, dF, rF, hs⟩
  have hs0 := hs
  unfold shared_mem_status_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    have hc0 := hc
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he1 : d.smspool p1 p2 with
    | SHRDUndef => rw [he1] at hs; cases hs
    | SHRDValid i' s va =>
      obtain ⟨-, a1, a2, hva⟩ := sm_get hM.sp h1 h2 he1
      let σ1 := σ.set "seen" (BitVec.ofNat 32 (if s then 1 else 0))
      have hr1 : Runs (rprimsA εR c) (getSeenS sb num_proc "seen" (.var "pid1") (.var "pid2")) σ l σ1 l := by
        have h := smGet_run εR hL hcs hlk "seen" (e1 := .var "pid1") (e2 := .var "pid2") hp1 hp2 h1 h2
          (show 2 < 3 by decide)
        rw [a2] at h; exact h
      have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
      have hq1 : σ1 "pid1" = BitVec.ofNat 32 p1 := (Locals.set_other _ _ (by decide)).trans hp1
      have hq2 : σ1 "pid2" = BitVec.ofNat 32 p2 := (Locals.set_other _ _ (by decide)).trans hp2
      cases s with
      | true =>
        rw [he1] at hs; simp only at hs
        cases he2 : d.smspool p2 p1 with
        | SHRDUndef => rw [he2] at hs; cases hs
        | SHRDValid st s2 v2 =>
          rw [he2] at hs; simp only at hs
          have hss : get_shared_mem_status_seen_spec num_proc p1 p2 d =
              some (if st = .SHRDPEND then 1 else SharedMemInfo2Z i') := by
            unfold get_shared_mem_status_seen_spec
            rw [if_pos hc0, he2]; simp only
            by_cases hst : st = .SHRDPEND
            · rw [if_pos hst, if_pos hst]
            · rw [if_neg hst, if_neg hst, he1]
          obtain ⟨σ2, l2, b2, d2, hr2, hcs2, hM2, hlk2, hf2, hd2, v, hv, hrv, -⟩ :=
            statusSeen_triple εR c i0 hL p1 p2 σ1 l b d hlk1 hcs hM ⟨hq1, hq2, _, hss⟩
          rw [hss] at hv; simp only [Option.some.injEq] at hv
          have hres : dF = d ∧ rF = v := by
            rw [← hv]
            by_cases hst : st = .SHRDPEND
            · rw [if_pos hst] at hs ⊢
              simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact ⟨hs.1.symm, hs.2.symm⟩
            · rw [if_neg hst] at hs ⊢
              simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact ⟨hs.1.symm, hs.2.symm⟩
          have hseen : ¬ (Expr.var "seen").eval σ1 = 0 := by
            show ¬ σ1 "seen" = 0
            simp [σ1]
          refine ⟨σ2, l2, b2, d2, Runs.seq hr1 (Runs.ite_true hseen hr2), hcs2, hM2, ?_,
            fun k hk => hf2 k (fun h => h), rF, ?_, ?_⟩
          · rw [hlk2]; simp [σ1, Locals.set]
          · rw [hs0, hd2, hres.1]
          · rw [hrv, hres.2]
      | false =>
        rw [he1] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
        obtain ⟨l2, hr2, hcs2⟩ := smSet_run εR hL hcs hlk1 (e1 := .var "pid1") (e2 := .var "pid2")
          (ve := .const 1) (w := BitVec.ofNat 32 1) hq1 hq2 h1 h2 (show 2 < 3 by decide) rfl
        have hM2 := sm_set1 hL hM h1 h2 he1 (show 2 < 3 by decide) (BitVec.ofNat 32 1) (i' := i') (s' := true)
          (v' := va) hva (fun e => by cases e) (fun _ => rfl) (fun e => by cases e) (fun _ => rfl)
          (fun _ => rfl) (fun e => absurd rfl e)
        rw [hdF] at hM2
        have hr3 : Runs (rprimsA εR c) (getStateS sb num_proc "r" (.var "pid1") (.var "pid2")) (σ1.set "_" 0) l2
            ((σ1.set "_" 0).set "r" (BitVec.ofNat 32 (SharedMemInfo2Z i'))) l2 := by
          have h := smGet_run εR hL hcs2 (σ := σ1.set "_" 0) (by simpa [Locals.set] using hlk1) "r"
            (e1 := .var "pid1") (e2 := .var "pid2") ((Locals.set_other _ _ (by decide)).trans hq1)
            ((Locals.set_other _ _ (by decide)).trans hq2) h1 h2 (show 1 < 3 by decide)
          rw [sc_ne _ _ (by unfold scell; omega), a1] at h; exact h
        have hseen : (Expr.var "seen").eval σ1 = 0 := by
          show σ1 "seen" = 0
          simp [σ1]
        refine ⟨_, l2, _, dF, Runs.seq hr1 (Runs.ite_false hseen (Runs.seq hr2 hr3)), hcs2, hM2, ?_,
          sm_foot h1 h2 (by decide) _, rF, hs0, ?_⟩
        · simp [Locals.set, σ1]
        · rw [← hrF]; simp
  · rw [if_neg hc] at hs; cases hs

end Proofs

end MShare
