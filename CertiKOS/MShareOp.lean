import CertiKOS.MShareIntro

/-!
# mCertiKOS `MShareOp`: the shared-memory transitions, ported

Ported from `objects/ObjShareMem.v`: `shared_mem_to_pending_spec`,
`shared_mem_to_dead_spec`, `shared_mem_to_ready_spec`,
`get_shared_mem_status_seen_spec`.

Ported from `mm/MShareIntroCSource.v`: the C code of the four functions.

* `toPending_triple`, `toDead_triple`, `statusSeen_triple`: each refines its
  specification.
* `toReady_triple`: **`shared_mem_to_ready` refines its specification.** It
  maps one fresh page in both processes with `pt_resv2`
  (`ptResv2_lift`, the page-table theorem carried to the state with the
  shared-memory table) and marks both directions ready.

The functions take their arguments in the locals `pid1`, `pid2`, `sva`.
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
open MALInit (rd_run wr_run asg_run tn)

/-! ## Specifications (`ObjShareMem.v`) -/

section Specs
variable (num_proc : Nat)

/-- Offer: `pid1` is waiting for `pid2`, with the address it offered. -/
def shared_mem_to_pending_spec (pid1 pid2 vadr : Nat) (d : SData) : Option SData :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid _ _ _ => some { d with smspool := smSet d.smspool pid1 pid2 (.SHRDValid .SHRDPEND true vadr) }
    | .SHRDUndef => none
  else none

/-- The sharing failed: both directions are dead, and `pid2` has not seen it. -/
def shared_mem_to_dead_spec (pid1 pid2 vadr : Nat) (d : SData) : Option SData :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2, d.smspool pid2 pid1 with
    | .SHRDValid _ _ _, .SHRDValid _ _ _ =>
      let smsp := smSet d.smspool pid1 pid2 (.SHRDValid .SHRDDEAD true 0)
      let smsp' := smSet smsp pid2 pid1 (.SHRDValid .SHRDDEAD false 0)
      some { d with smspool := smsp' }
    | _, _ => none
  else none

/-- Map a fresh page at `vadr` in `pid1` and at the address `pid2` offered.
If that worked, both directions are ready, and `pid2` has not seen it. -/
def shared_mem_to_ready_spec (maxpage : Nat) (pid1 pid2 vadr : Nat) (d : SData) : Option (SData × Nat) :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid _ _ _ =>
      match d.smspool pid2 pid1 with
      | .SHRDValid _ _ vadr' =>
        if vadr' < 2 ^ 32 then
          match ptResv2_spec maxpage num_proc pid1 vadr 7 pid2 vadr' 7 d.toPTData with
          | some (pt', rest) =>
            if rest = maxpage + 1 then some ({ d with toPTData := pt' }, maxpage + 1)
            else
              let smsp := smSet d.smspool pid1 pid2 (.SHRDValid .SHRDREADY true 0)
              let smsp' := smSet smsp pid2 pid1 (.SHRDValid .SHRDREADY false 0)
              some (⟨pt', smsp'⟩, rest)
          | none => none
        else none
      | .SHRDUndef => none
    | .SHRDUndef => none
  else none

/-- The state `pid1` sees: pending if `pid2` is waiting for it, its own state
otherwise. -/
def get_shared_mem_status_seen_spec (pid1 pid2 : Nat) (d : SData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid2 pid1 with
    | .SHRDValid st _ _ =>
      if st = .SHRDPEND then some 1
      else
        match d.smspool pid1 pid2 with
        | .SHRDValid i' _ _ => some (SharedMemInfo2Z i')
        | .SHRDUndef => none
    | .SHRDUndef => none
  else none

end Specs

/-! ## The C code (`MShareIntroCSource.v`) -/

/-- `shared_mem_to_pending(pid1, pid2, vadr)`:
`set_shared_mem_state(pid1, pid2, 1); set_shared_mem_seen(pid1, pid2, 1); set_shared_mem_loc(pid1, pid2, vadr);` -/
def toPendingS (sb n : Nat) : Stmt APrim :=
  .seq (setStateS sb n (.var "pid1") (.var "pid2") (.const 1))
    (.seq (setSeenS sb n (.var "pid1") (.var "pid2") (.const 1))
      (setLocS sb n (.var "pid1") (.var "pid2") (.var "sva")))

/-- `shared_mem_to_dead(pid1, pid2, vadr)`: state 2, seen 1, loc 0 for
`(pid1, pid2)`; state 2, seen 0, loc 0 for `(pid2, pid1)`. -/
def toDeadS (sb n : Nat) : Stmt APrim :=
  .seq (setStateS sb n (.var "pid1") (.var "pid2") (.const 2))
    (.seq (setSeenS sb n (.var "pid1") (.var "pid2") (.const 1))
      (.seq (setLocS sb n (.var "pid1") (.var "pid2") (.const 0))
        (.seq (setStateS sb n (.var "pid2") (.var "pid1") (.const 2))
          (.seq (setSeenS sb n (.var "pid2") (.var "pid1") (.const 0))
            (setLocS sb n (.var "pid2") (.var "pid1") (.const 0))))))

/-- The six writes of `shared_mem_to_ready` when `pt_resv2` succeeded. -/
def readyTailS (sb n : Nat) : Stmt APrim :=
  .seq (setStateS sb n (.var "pid1") (.var "pid2") (.const 0))
    (.seq (setSeenS sb n (.var "pid1") (.var "pid2") (.const 1))
      (.seq (setLocS sb n (.var "pid1") (.var "pid2") (.const 0))
        (.seq (setStateS sb n (.var "pid2") (.var "pid1") (.const 0))
          (.seq (setSeenS sb n (.var "pid2") (.var "pid1") (.const 0))
            (setLocS sb n (.var "pid2") (.var "pid1") (.const 0))))))

/-- ```
dest_va = get_shared_mem_loc(pid2, pid1);
res = pt_resv2(pid1, vadr, 7, pid2, dest_va, 7);
if (res == MAGIC_NUMBER) { }
else { ... six writes ... }
return res;
```
`pt_resv2`'s arguments are passed by assigning its parameter locals. -/
def toReadyS (cb maxpage pb fb sb n : Nat) : Stmt APrim :=
  .seq (getLocS sb n "dva" (.var "pid2") (.var "pid1"))
  (.seq (.assign "n" (.var "pid1")) (.seq (.assign "vaddr" (.var "sva")) (.seq (.assign "perm" (.const 7))
  (.seq (.assign "n2" (.var "pid2")) (.seq (.assign "vaddr2" (.var "dva")) (.seq (.assign "perm2" (.const 7))
  (.seq (ptResv2S cb maxpage pb fb) (.seq (.assign "rs" (.var "r"))
  (.seq (.ite (.bin .eq (.var "rs") (.const (BitVec.ofNat 32 (maxpage + 1)))) .skip (readyTailS sb n))
    (.assign "r" (.var "rs")))))))))))

/-- ```
ds_state = get_shared_mem_state(pid2, pid1);
if (ds_state == 1) res = 1; else res = get_shared_mem_state(pid1, pid2);
return res;
``` -/
def statusSeenS (sb n : Nat) : Stmt APrim :=
  .seq (getStateS sb n "ds" (.var "pid2") (.var "pid1"))
    (.ite (.bin .eq (.var "ds") (.const 1)) (.assign "r" (.const 1))
      (getStateS sb n "r" (.var "pid1") (.var "pid2")))

section Proofs
variable {maxpage num_id cb num_proc pb ib fb ida sb : Nat}

/-- **`shared_mem_to_pending` refines its specification.** -/
theorem toPending_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (p1 p2 va : Nat) (hva : va < 2 ^ 32) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun σ d => σ "pid1" = BitVec.ofNat 32 p1 ∧ σ "pid2" = BitVec.ofNat 32 p2 ∧
        σ "sva" = BitVec.ofNat 32 va ∧ ∃ d1, shared_mem_to_pending_spec num_proc p1 p2 va d = some d1)
      (toPendingS sb num_proc)
      (fun σ d σ' d' => shared_mem_to_pending_spec num_proc p1 p2 va d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨hp1, hp2, hsva, d1, hs⟩
  have hs0 := hs
  unfold shared_mem_to_pending_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he : d.smspool p1 p2 with
    | SHRDUndef => rw [he] at hs; cases hs
    | SHRDValid i s v0 =>
      rw [he] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨l', b', hr, hcs', hM', hf, -⟩ := sm_write3 εR hL hcs hlk hM (a1 := "pid1") (a2 := "pid2")
        (by decide) (by decide) hp1 hp2 h1 h2
        (k1 := 1) (k2 := 2) (k3 := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (v1 := .const 1) (v2 := .const 1) (v3 := .var "sva") (w1 := BitVec.ofNat 32 1)
        (w2 := BitVec.ofNat 32 1) (w3 := BitVec.ofNat 32 va) rfl rfl
        ((Locals.set_other _ _ (by decide)).trans hsva) (i := .SHRDPEND) (s := true) (v := va) hva
        (by
          rintro k w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨(fun e => by cases e), fun _ => rfl, (fun e => by cases e)⟩
          · exact ⟨(fun e => by cases e), (fun e => by cases e), fun _ => rfl⟩
          · exact ⟨fun _ => rfl, (fun e => by cases e), (fun e => by cases e)⟩)
      rw [hs] at hM'
      exact ⟨_, l', b', d1, hr, hcs', hM', Locals.set_other _ _ (by decide), hf, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- The six writes that set both directions to `st`, the second unseen. -/
theorem both_run (εR : REnv) {c : CPU} {i0 : Nat} (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) {d : SData}
    (hM : MatchS maxpage num_id cb num_proc pb ib fb ida sb d b) {p1 p2 : Nat}
    (hp1 : σ "pid1" = BitVec.ofNat 32 p1) (hp2 : σ "pid2" = BitVec.ofNat 32 p2) (h1 : p1 < num_proc)
    (h2 : p2 < num_proc) (st : SharedMemInfo) :
    ∃ l' b', Runs (rprimsA εR c)
        (.seq (setStateS sb num_proc (.var "pid1") (.var "pid2") (.const (BitVec.ofNat 32 (SharedMemInfo2Z st))))
          (.seq (setSeenS sb num_proc (.var "pid1") (.var "pid2") (.const 1))
            (.seq (setLocS sb num_proc (.var "pid1") (.var "pid2") (.const 0))
              (.seq (setStateS sb num_proc (.var "pid2") (.var "pid1")
                  (.const (BitVec.ofNat 32 (SharedMemInfo2Z st))))
                (.seq (setSeenS sb num_proc (.var "pid2") (.var "pid1") (.const 0))
                  (setLocS sb num_proc (.var "pid2") (.var "pid1") (.const 0)))))))
        σ l (σ.set "_" 0) l' ∧ CS1 c i0 l' b' ∧
      MatchS maxpage num_id cb num_proc pb ib fb ida sb
        { d with smspool := smSet (smSet d.smspool p1 p2 (.SHRDValid st true 0)) p2 p1 (.SHRDValid st false 0) }
        b' ∧
      ∀ k, ¬ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)) → b' k = b k := by
  obtain ⟨l1, b1, -, c1, hM1, hf1, hK⟩ := sm_write3 εR hL hcs hlk hM (a1 := "pid1") (a2 := "pid2")
    (by decide) (by decide) hp1 hp2 h1 h2
    (k1 := 1) (k2 := 2) (k3 := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (v1 := .const (BitVec.ofNat 32 (SharedMemInfo2Z st))) (v2 := .const 1) (v3 := .const 0)
    (w1 := BitVec.ofNat 32 (SharedMemInfo2Z st)) (w2 := BitVec.ofNat 32 1) (w3 := BitVec.ofNat 32 0)
    rfl rfl rfl (i := st) (s := true) (v := 0) (by decide)
    (by
      rintro k w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨(fun e => by cases e), fun _ => rfl, (fun e => by cases e)⟩
      · exact ⟨(fun e => by cases e), (fun e => by cases e), fun _ => rfl⟩
      · exact ⟨fun _ => rfl, (fun e => by cases e), (fun e => by cases e)⟩)
  have hlk1 : ((σ.set "_" 0) "lk").toNat = i0 := by simpa [Locals.set] using hlk
  obtain ⟨l2, b2, hr2, c2, hM2, hf2, -⟩ := sm_write3 εR hL c1 hlk1 hM1 (a1 := "pid2") (a2 := "pid1")
    (by decide) (by decide) ((Locals.set_other _ _ (by decide)).trans hp2)
    ((Locals.set_other _ _ (by decide)).trans hp1) h2 h1
    (k1 := 1) (k2 := 2) (k3 := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (v1 := .const (BitVec.ofNat 32 (SharedMemInfo2Z st))) (v2 := .const 0) (v3 := .const 0)
    (w1 := BitVec.ofNat 32 (SharedMemInfo2Z st)) (w2 := BitVec.ofNat 32 0) (w3 := BitVec.ofNat 32 0)
    rfl rfl rfl (i := st) (s := false) (v := 0) (by decide)
    (by
      rintro k w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨(fun e => by cases e), fun _ => rfl, (fun e => by cases e)⟩
      · exact ⟨(fun e => by cases e), (fun e => by cases e), fun _ => rfl⟩
      · exact ⟨fun _ => rfl, (fun e => by cases e), (fun e => by cases e)⟩)
  have hrun := hK _ _ _ hr2
  rw [show (σ.set "_" 0).set "_" 0 = σ.set "_" 0 from set_set _ _ _ _] at hrun
  exact ⟨l2, b2, hrun, c2, hM2, fun k hk => by rw [hf2 k hk, hf1 k hk]⟩

/-- **`shared_mem_to_dead` refines its specification.** -/
theorem toDead_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (p1 p2 va : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun σ d => σ "pid1" = BitVec.ofNat 32 p1 ∧ σ "pid2" = BitVec.ofNat 32 p2 ∧
        ∃ d1, shared_mem_to_dead_spec num_proc p1 p2 va d = some d1)
      (toDeadS sb num_proc)
      (fun σ d σ' d' => shared_mem_to_dead_spec num_proc p1 p2 va d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨hp1, hp2, d1, hs⟩
  have hs0 := hs
  unfold shared_mem_to_dead_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he1 : d.smspool p1 p2 with
    | SHRDUndef => rw [he1] at hs; cases hs
    | SHRDValid i1 s1 v1 =>
      cases he2 : d.smspool p2 p1 with
      | SHRDUndef => rw [he1, he2] at hs; cases hs
      | SHRDValid i2 s2 v2 =>
        rw [he1, he2] at hs; simp only [Option.some.injEq] at hs
        obtain ⟨l', b', hr, hcs', hM', hf⟩ := both_run εR hL hcs hlk hM hp1 hp2 h1 h2 .SHRDDEAD
        rw [hs] at hM'
        exact ⟨_, l', b', d1, hr, hcs', hM', Locals.set_other _ _ (by decide), hf, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`get_shared_mem_status_seen` refines its specification.** -/
theorem statusSeen_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : SLayout maxpage num_id cb num_proc pb ib fb sb) (p1 p2 : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb) (fun _ => False)
      (fun σ d => σ "pid1" = BitVec.ofNat 32 p1 ∧ σ "pid2" = BitVec.ofNat 32 p2 ∧
        ∃ v, get_shared_mem_status_seen_spec num_proc p1 p2 d = some v)
      (statusSeenS sb num_proc)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_shared_mem_status_seen_spec num_proc p1 p2 d = some v ∧
        σ' "r" = BitVec.ofNat 32 v ∧ ∀ z, z ≠ "ds" → z ≠ "r" → σ' z = σ z) := by
  intro σ l b d hlk hcs hM ⟨hp1, hp2, v, hs⟩
  have hs0 := hs
  unfold get_shared_mem_status_seen_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he2 : d.smspool p2 p1 with
    | SHRDUndef => rw [he2] at hs; cases hs
    | SHRDValid st s2 v2 =>
      rw [he2] at hs; simp only at hs
      obtain ⟨-, a1, -, -⟩ := sm_get hM.sp h2 h1 he2
      let σ1 := σ.set "ds" (BitVec.ofNat 32 (SharedMemInfo2Z st))
      have hr1 : Runs (rprimsA εR c) (getStateS sb num_proc "ds" (.var "pid2") (.var "pid1")) σ l σ1 l := by
        have h := smGet_run εR hL hcs hlk "ds" (e1 := .var "pid2") (e2 := .var "pid1") hp2 hp1 h2 h1
          (show 1 < 3 by decide)
        rw [a1] at h; exact h
      by_cases hst : st = .SHRDPEND
      · rw [if_pos hst] at hs; simp only [Option.some.injEq] at hs
        subst hst
        refine ⟨_, l, b, d, Runs.seq hr1 (Runs.ite_true (eq_true (by simp [σ1]; rfl)) (Runs.assign _ _)),
          hcs, hM, ?_, fun _ _ => rfl, rfl, v, hs0, ?_, fun z hz1 hz2 => ?_⟩
        · simp [Locals.set, σ1]
        · rw [← hs]; simp [Locals.set]; rfl
        · rw [Locals.set_other _ _ hz2]; simp [σ1, Locals.set, hz1]
      · rw [if_neg hst] at hs
        cases he1 : d.smspool p1 p2 with
        | SHRDUndef => rw [he1] at hs; cases hs
        | SHRDValid i1 s1 v1 =>
          rw [he1] at hs; simp only [Option.some.injEq] at hs
          obtain ⟨-, c1, -, -⟩ := sm_get hM.sp h1 h2 he1
          have hne : σ1 "ds" ≠ 1 := by
            have h : (BitVec.ofNat 32 (SharedMemInfo2Z st) : Val) ≠ BitVec.ofNat 32 1 := by
              cases st
              · decide
              · exact absurd rfl hst
              · decide
            simpa [σ1] using h
          have hr2 : Runs (rprimsA εR c) (getStateS sb num_proc "r" (.var "pid1") (.var "pid2")) σ1 l
              (σ1.set "r" (BitVec.ofNat 32 (SharedMemInfo2Z i1))) l := by
            have h := smGet_run εR hL hcs (σ := σ1) (by simpa [σ1, Locals.set] using hlk) "r"
              (e1 := .var "pid1") (e2 := .var "pid2") ((Locals.set_other _ _ (by decide)).trans hp1)
              ((Locals.set_other _ _ (by decide)).trans hp2) h1 h2 (show 1 < 3 by decide)
            rw [c1] at h; exact h
          refine ⟨_, l, b, d, Runs.seq hr1 (Runs.ite_false (eq_false hne) hr2), hcs, hM, ?_,
            fun _ _ => rfl, rfl, v, hs0, ?_, fun z hz1 hz2 => ?_⟩
          · simp [Locals.set, σ1]
          · rw [← hs]; simp
          · rw [Locals.set_other _ _ hz2]; simp [σ1, Locals.set, hz1]
  · rw [if_neg hc] at hs; cases hs

/-- **`pt_resv2` in the state with the shared-memory table.** It leaves the
table alone. -/
theorem ptResv2_lift (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (nn vadr perm nn' vadr' perm' : Nat) (hnid : nn < num_id) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb) (fun k => k < cb + 5 * num_id ∨ pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        σ "perm" = BitVec.ofNat 32 perm ∧ σ "n2" = BitVec.ofNat 32 nn' ∧
        σ "vaddr2" = BitVec.ofNat 32 vadr' ∧ σ "perm2" = BitVec.ofNat 32 perm' ∧
        ATInv maxpage kl kh d.toPData ∧ UQ d.AC ∧
        ∃ d1 r, ptResv2_spec maxpage num_proc nn vadr perm nn' vadr' perm' d.toPTData = some (d1, r))
      (ptResv2S cb maxpage pb fb)
      (fun _ d σ' d' => ∃ pt' : PTData, d' = { d with toPTData := pt' } ∧
        ∃ r, ptResv2_spec maxpage num_proc nn vadr perm nn' vadr' perm' d.toPTData = some (pt', r) ∧
          σ' "r" = BitVec.ofNat 32 r) := by
  have := hL.hsb; have := hL.hse
  refine ((ptResv2_triple εR c i0 hL.lay hmax hnum hmp hnn (kl := kl) (kh := kh) nn vadr perm nn' vadr'
      perm' hnid).lift (π := SData.toPTData)
    (put := fun (d' : SData) (pt : PTData) => ({ d' with toPTData := pt } : SData))
    (M2 := fun d' b => MatchSP num_proc sb d'.smspool b) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.all, h.sp⟩, fun h => ⟨h.1, h.2⟩⟩)
  intro d' b σ σ' d1 b' h2 hM hP hQ hf q1 q2 g1 g2
  have hlt := scell_lt (sb := sb) g1 g2 (show 2 < 3 by decide)
  have e : ∀ k, k < 3 → b' (scell sb num_proc q1 q2 k) = b (scell sb num_proc q1 q2 k) := fun k hk =>
    hf _ (by unfold scell at *; omega)
  show MatchSMS (d'.smspool q1 q2) _ _ _
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
  exact h2 q1 q2 g1 g2

end Proofs

end MShare
