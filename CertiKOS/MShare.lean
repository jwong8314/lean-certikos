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

/-- **`offer_shared_mem` refines its specification.** -/
theorem offer_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (p1 p2 va : Nat) (hva : va < 2 ^ 32) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => (k < cb + 5 * num_id ∨ pb ≤ k) ∨ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)))
      (fun σ d => σ "pid1" = BitVec.ofNat 32 p1 ∧ σ "pid2" = BitVec.ofNat 32 p2 ∧
        σ "sva" = BitVec.ofNat 32 va ∧ ATInv maxpage kl kh d.toPData ∧ UQ d.AC ∧
        ∃ d1 r, offer_shared_mem_spec num_proc maxpage p1 p2 va d = some (d1, r))
      (offerS cb maxpage pb fb sb num_proc)
      (fun σ d σ' d' => ∃ r, offer_shared_mem_spec num_proc maxpage p1 p2 va d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hp1, hp2, hsva, hI, hu, dF, rF, hs⟩
  have hs0 := hs
  have hmagic : maxpage + 1 < 2 ^ 32 := by omega
  unfold offer_shared_mem_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    have hc0 := hc
    obtain ⟨hpg, hipt, h1, h2, hne12⟩ := hc
    cases he1 : d.smspool p1 p2 with
    | SHRDUndef => rw [he1] at hs; cases hs
    | SHRDValid st s1 v1 =>
      rw [he1] at hs; simp only at hs
      obtain ⟨-, a1, -, -⟩ := sm_get hM.sp h1 h2 he1
      -- sd_state = get_shared_mem_state(source, dest)
      let σ1 := σ.set "sd" (BitVec.ofNat 32 (SharedMemInfo2Z st))
      have hr1 : Runs (rprimsA εR c) (getStateS sb num_proc "sd" (.var "pid1") (.var "pid2")) σ l σ1 l := by
        have h := smGet_run εR hL hcs hlk "sd" (e1 := .var "pid1") (e2 := .var "pid2") hp1 hp2 h1 h2
          (show 1 < 3 by decide)
        rw [a1] at h; exact h
      have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
      have hq1 : σ1 "pid1" = BitVec.ofNat 32 p1 := (Locals.set_other _ _ (by decide)).trans hp1
      have hq2 : σ1 "pid2" = BitVec.ofNat 32 p2 := (Locals.set_other _ _ (by decide)).trans hp2
      have hq3 : σ1 "sva" = BitVec.ofNat 32 va := (Locals.set_other _ _ (by decide)).trans hsva
      by_cases hst : st = .SHRDPEND
      · rw [if_pos hst] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
        subst hst
        refine ⟨_, l, b, d, Runs.seq hr1 (Runs.ite_true (eq_true (by simp [σ1]; rfl)) (Runs.assign _ _)),
          hcs, hM, ?_, fun _ _ => rfl, 1, by rw [hs0, hdF, hrF], ?_⟩
        · simp [Locals.set, σ1]
        · simp [Locals.set]; rfl
      · rw [if_neg hst] at hs
        have hsd : σ1 "sd" ≠ 1 := by
          have h : (BitVec.ofNat 32 (SharedMemInfo2Z st) : Val) ≠ BitVec.ofNat 32 1 := by
            cases st
            · decide
            · exact absurd rfl hst
            · decide
          simpa [σ1] using h
        cases he2 : d.smspool p2 p1 with
        | SHRDUndef => rw [he2] at hs; cases hs
        | SHRDValid st' s2 v2 =>
          rw [he2] at hs; simp only at hs
          obtain ⟨-, c1, -, hv2⟩ := sm_get hM.sp h2 h1 he2
          rw [if_pos hv2] at hs
          -- ds_state = get_shared_mem_state(dest, source)
          let σ2 := σ1.set "ds" (BitVec.ofNat 32 (SharedMemInfo2Z st'))
          have hr2 : Runs (rprimsA εR c) (getStateS sb num_proc "ds" (.var "pid2") (.var "pid1")) σ1 l σ2 l := by
            have h := smGet_run εR hL hcs hlk1 "ds" (e1 := .var "pid2") (e2 := .var "pid1") hq2 hq1 h2 h1
              (show 1 < 3 by decide)
            rw [c1] at h; exact h
          have hlk2 : (σ2 "lk").toNat = i0 := by simpa [σ2, Locals.set] using hlk1
          have ht1 : σ2 "pid1" = BitVec.ofNat 32 p1 := (Locals.set_other _ _ (by decide)).trans hq1
          have ht2 : σ2 "pid2" = BitVec.ofNat 32 p2 := (Locals.set_other _ _ (by decide)).trans hq2
          have ht3 : σ2 "sva" = BitVec.ofNat 32 va := (Locals.set_other _ _ (by decide)).trans hq3
          have hpre : ∀ {τ : Locals} {lt : RLog},
              Runs (rprimsA εR c) (.ite (.bin .eq (.var "ds") (.const 1))
                (.seq (toReadyS cb maxpage pb fb sb num_proc) (.seq (.assign "isr" (.var "r"))
                  (.ite (.bin .eq (.var "isr") (.const (BitVec.ofNat 32 (maxpage + 1))))
                    (.seq (toDeadS sb num_proc) (.assign "r" (.const 2)))
                    (.assign "r" (.const 0)))))
                (.seq (toPendingS sb num_proc) (.assign "r" (.const 1)))) σ2 l τ lt →
              Runs (rprimsA εR c) (offerS cb maxpage pb fb sb num_proc) σ l τ lt := fun hS =>
            Runs.seq hr1 (Runs.ite_false (eq_false hsd) (Runs.seq hr2 hS))
          by_cases hst' : st' = .SHRDPEND
          · rw [if_pos hst'] at hs
            have hds : σ2 "ds" = 1 := by subst hst'; simp [σ2]; rfl
            cases hR : ptResv2_spec maxpage num_proc p1 va 7 p2 v2 7 d.toPTData with
            | none => rw [hR] at hs; cases hs
            | some pr =>
              obtain ⟨pt', re⟩ := pr
              rw [hR] at hs; simp only at hs
              obtain ⟨fpg, fipt⟩ := ptResv2_flags hR
              obtain ⟨-, -, hreb⟩ := ptResv2_keeps hI hR
              by_cases hre : re = maxpage + 1
              · rw [if_pos hre] at hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
                have hrdy : shared_mem_to_ready_spec num_proc maxpage p1 p2 va d =
                    some ({ d with toPTData := pt' }, maxpage + 1) := by
                  unfold shared_mem_to_ready_spec
                  rw [if_pos hc0, he1]; simp only
                  rw [he2]; simp only
                  rw [if_pos hv2, hR]; simp only
                  rw [if_pos hre]
                obtain ⟨σ3, l3, b3, d3, hr3, hcs3, hM3, hlk3, hf3, r, hsr, hrr, e1, e2, e3⟩ :=
                  toReady_triple εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh) p1 p2 va σ2 l b d hlk2 hcs
                    hM ⟨ht1, ht2, ht3, hI, hu, _, _, hrdy⟩
                rw [hrdy] at hsr
                simp only [Option.some.injEq, Prod.mk.injEq] at hsr; obtain ⟨hd3, hr3e⟩ := hsr
                rw [← hr3e] at hrr
                let σ4 := σ3.set "isr" (BitVec.ofNat 32 (maxpage + 1))
                have g4 : Runs (rprimsA εR c) (.assign "isr" (.var "r")) σ3 l3 σ4 l3 := asg_run _ _ hrr
                have hdead : shared_mem_to_dead_spec num_proc p1 p2 va d3 = some dF := by
                  rw [← hd3, ← hdF]
                  unfold shared_mem_to_dead_spec
                  have hc3 : pt'.pg = true ∧ pt'.ipt = true ∧ shared_mem_arg num_proc p1 p2 :=
                    ⟨fpg.trans hpg, fipt.trans hipt, h1, h2, hne12⟩
                  rw [if_pos hc3]
                  show (match d.smspool p1 p2, d.smspool p2 p1 with
                    | .SHRDValid _ _ _, .SHRDValid _ _ _ => _
                    | _, _ => none) = _
                  rw [he1, he2]
                obtain ⟨σ5, l5, b5, d5, hr5, hcs5, hM5, hlk5, hf5, hq5, hσ5⟩ :=
                  toDead_triple εR c i0 hL p1 p2 va σ4 l3 b3 d3
                    (by simp [σ4, Locals.set, hlk3, hlk2]) hcs3 hM3
                    ⟨by simp [σ4, Locals.set, e1, ht1], by simp [σ4, Locals.set, e2, ht2], _, hdead⟩
                rw [hdead] at hq5; simp only [Option.some.injEq] at hq5
                rw [← hq5] at hM5
                refine ⟨_, l5, b5, dF, hpre (Runs.ite_true (eq_true hds) (Runs.seq hr3 (Runs.seq g4
                  (Runs.ite_true (eq_true (by simp [σ4])) (Runs.seq hr5 (Runs.assign _ _)))))), hcs5, hM5, ?_,
                  fun k hk => ?_, 2, by rw [hs0, hrF], ?_⟩
                · simp [Locals.set, hlk5, σ4, hlk3, σ2, σ1]
                · rw [hf5 k (fun h => hk (Or.inr h)), hf3 k hk]
                · simp [Locals.set]; rfl
              · rw [if_neg hre] at hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
                have hrdy : shared_mem_to_ready_spec num_proc maxpage p1 p2 va d = some (dF, re) := by
                  rw [← hdF]
                  unfold shared_mem_to_ready_spec
                  rw [if_pos hc0, he1]; simp only
                  rw [he2]; simp only
                  rw [if_pos hv2, hR]; simp only
                  rw [if_neg hre]
                obtain ⟨σ3, l3, b3, d3, hr3, hcs3, hM3, hlk3, hf3, r, hsr, hrr, e1, e2, e3⟩ :=
                  toReady_triple εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh) p1 p2 va σ2 l b d hlk2 hcs
                    hM ⟨ht1, ht2, ht3, hI, hu, _, _, hrdy⟩
                rw [hrdy] at hsr
                simp only [Option.some.injEq, Prod.mk.injEq] at hsr; obtain ⟨hd3, hr3e⟩ := hsr
                rw [← hr3e] at hrr; rw [← hd3] at hM3
                let σ4 := σ3.set "isr" (BitVec.ofNat 32 re)
                have g4 : Runs (rprimsA εR c) (.assign "isr" (.var "r")) σ3 l3 σ4 l3 := asg_run _ _ hrr
                have hisr : σ4 "isr" ≠ BitVec.ofNat 32 (maxpage + 1) := by
                  have h : (BitVec.ofNat 32 re : Val) ≠ BitVec.ofNat 32 (maxpage + 1) :=
                    KernPAlloc.ofNat_ne (a := re) (b := maxpage + 1) (by omega) hmagic hre
                  simpa [σ4] using h
                refine ⟨_, l3, b3, dF, hpre (Runs.ite_true (eq_true hds) (Runs.seq hr3 (Runs.seq g4
                  (Runs.ite_false (eq_false hisr) (Runs.assign _ _))))), hcs3, hM3, ?_, hf3, 0,
                  by rw [hs0, hrF], ?_⟩
                · simp [Locals.set, σ4, hlk3, σ2, σ1]
                · simp [Locals.set]; rfl
          · rw [if_neg hst'] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
            have hds : σ2 "ds" ≠ 1 := by
              have h : (BitVec.ofNat 32 (SharedMemInfo2Z st') : Val) ≠ BitVec.ofNat 32 1 := by
                cases st'
                · decide
                · exact absurd rfl hst'
                · decide
              simpa [σ2] using h
            have hpend : shared_mem_to_pending_spec num_proc p1 p2 va d = some dF := by
              rw [← hdF]
              unfold shared_mem_to_pending_spec
              rw [if_pos hc0, he1]
            obtain ⟨σ3, l3, b3, d3, hr3, hcs3, hM3, hlk3, hf3, hq3', hσ3⟩ :=
              toPending_triple εR c i0 hL p1 p2 va hva σ2 l b d hlk2 hcs hM ⟨ht1, ht2, ht3, _, hpend⟩
            rw [hpend] at hq3'; simp only [Option.some.injEq] at hq3'
            rw [← hq3'] at hM3
            refine ⟨_, l3, b3, dF, hpre (Runs.ite_false (eq_false hds) (Runs.seq hr3 (Runs.assign _ _))),
              hcs3, hM3, ?_, fun k hk => hf3 k (fun h => hk (Or.inr h)), 1, by rw [hs0, hrF], ?_⟩
            · simp [Locals.set, hlk3, σ2, σ1]
            · simp [Locals.set]; rfl
  · rw [if_neg hc] at hs; cases hs

end Proofs

/-! ## `shared_mem_init` (`CalRealSMSPool.v`, `MShareIntroCSource.v`) -/

def Calculate_smsp_inner_at_j (i j : Nat) (smsp : SharedMemSTPool) : SharedMemSTPool :=
  smSet smsp i j (.SHRDValid .SHRDDEAD true 0)

def Calculate_smsp_inner (i : Nat) : Nat → SharedMemSTPool → SharedMemSTPool
  | 0, smsp => Calculate_smsp_inner_at_j i 0 smsp
  | k + 1, smsp => Calculate_smsp_inner_at_j i (k + 1) (Calculate_smsp_inner i k smsp)

def Calculate_smsp_at_i (num_proc i : Nat) (smsp : SharedMemSTPool) : SharedMemSTPool :=
  Calculate_smsp_inner i (num_proc - 1) smsp

def Calculate_smsp (num_proc : Nat) : Nat → SharedMemSTPool → SharedMemSTPool
  | 0, smsp => Calculate_smsp_at_i num_proc 0 smsp
  | k + 1, smsp => Calculate_smsp_at_i num_proc (k + 1) (Calculate_smsp num_proc k smsp)

/-- `real_smspool`: every entry dead and seen. -/
def real_smspool (num_proc : Nat) (smsp : SharedMemSTPool) : SharedMemSTPool :=
  Calculate_smsp num_proc (num_proc - 1) smsp

/-- **`sharedmem_init_spec`** (`ObjShareMem.v`), with the allocation table in
place of the owner lists. -/
def sharedmem_init_spec (num_proc kl kh : Nat) (mm : MALInit.MMTable) (size : Nat) (d : SData) : Option SData :=
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
      smspool := real_smspool num_proc d.smspool }
  else none

/-- Row `i` with its first `j` entries cleared. -/
def rowS (i : Nat) : Nat → SharedMemSTPool → SharedMemSTPool
  | 0, s => s
  | j + 1, s => Calculate_smsp_inner_at_j i j (rowS i j s)

theorem rowS_calc (i : Nat) (s : SharedMemSTPool) : ∀ k, Calculate_smsp_inner i k s = rowS i (k + 1) s
  | 0 => rfl
  | k + 1 => by
    show Calculate_smsp_inner_at_j i (k + 1) (Calculate_smsp_inner i k s) = _
    rw [rowS_calc i s k]; rfl

/-- The first `m` rows cleared. -/
def allS (n : Nat) : Nat → SharedMemSTPool → SharedMemSTPool
  | 0, s => s
  | m + 1, s => rowS m n (allS n m s)

theorem allS_calc (n : Nat) (s : SharedMemSTPool) : ∀ k, Calculate_smsp (n + 1) k s = allS (n + 1) (k + 1) s
  | 0 => rowS_calc 0 s n
  | k + 1 => by
    show Calculate_smsp_inner (k + 1) n (Calculate_smsp (n + 1) k s) = _
    rw [allS_calc n s k, rowS_calc]; rfl

theorem allS_real {n : Nat} (h : 0 < n) (s : SharedMemSTPool) : real_smspool n s = allS n n s := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact allS_calc k s k

def Ds (d : SData) (sp : SharedMemSTPool) : SData := { d with smspool := sp }

theorem clear_step {num_proc : Nat} {d : SData} (hpg : d.pg = true) (hipt : d.ipt = true) {i j : Nat}
    (hi : i < num_proc) (hj : j < num_proc) (sp : SharedMemSTPool) :
    clear_shared_mem_spec num_proc i j (Ds d sp) = some (Ds d (Calculate_smsp_inner_at_j i j sp)) := by
  unfold clear_shared_mem_spec
  rw [if_pos ⟨hpg, hipt, hi, hj⟩]; rfl

/-- `while (j < num_proc) { clear_shared_mem(i, j); j++; }` -/
def smInitInner (sb n : Nat) : Stmt APrim :=
  .while (.bin .ltu (.var "j") (.const (BitVec.ofNat 32 n)))
    (.seq (clearS sb n (.var "i") (.var "j")) (.assign "j" (.bin .add (.var "j") (.const 1))))

def smInitBody (sb n : Nat) : Stmt APrim :=
  .seq (.assign "j" (.const 0)) (.seq (smInitInner sb n) (.assign "i" (.bin .add (.var "i") (.const 1))))

/-- The loops of `shared_mem_init`:
`i = 0; while (i < num_proc) { j = 0; while (j < num_proc) { clear_shared_mem(i, j); j++; } i++; }` -/
def smInitLoop (sb n : Nat) : Stmt APrim :=
  .seq (.assign "i" (.const 0)) (.while (.bin .ltu (.var "i") (.const (BitVec.ofNat 32 n))) (smInitBody sb n))

section Init
variable {maxpage num_id cb num_proc pb ib fb ida sb : Nat}

theorem smInitInner_run (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    {d : SData} (hpg : d.pg = true) (hipt : d.ipt = true) {x : Nat} (hx : x < num_proc)
    (sp : SharedMemSTPool) (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MatchS maxpage num_id cb num_proc pb ib fb ida sb (Ds d sp) b)
    (hi : σ "i" = BitVec.ofNat 32 x) (hj : σ "j" = 0) :
    ∃ σ' l' b', Runs (rprimsA εR c) (smInitInner sb num_proc) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MatchS maxpage num_id cb num_proc pb ib fb ida sb (Ds d (rowS x num_proc sp)) b' ∧
      σ' "lk" = σ "lk" ∧ σ' "i" = σ "i" ∧
      ∀ k, ¬ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)) → b' k = b k := by
  have hnp : num_proc < 2 ^ 32 := by
    have := hL.hse; have := hL.lay.hib; have := hL.lay.hfb; have := hL.lay.hend
    have := Nat.le_mul_self num_proc
    omega
  let Inv : Locals → RLog → Prop := fun τ l' => τ "lk" = σ "lk" ∧ τ "i" = BitVec.ofNat 32 x ∧
    ∃ m b', m ≤ num_proc ∧ τ "j" = BitVec.ofNat 32 m ∧ CS1 c i0 l' b' ∧
      MatchS maxpage num_id cb num_proc pb ib fb ida sb (Ds d (rowS x m sp)) b' ∧
      ∀ k, ¬ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)) → b' k = b k
  have hbody : ∀ τ l', Inv τ l' → ¬ (Expr.bin .ltu (.var "j") (.const (BitVec.ofNat 32 num_proc))).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (.seq (clearS sb num_proc (.var "i") (.var "j"))
          (.assign "j" (.bin .add (.var "j") (.const 1)))) τ l' τ' l'' ∧ Inv τ' l'' ∧
        num_proc - (τ' "j").toNat < num_proc - (τ "j").toNat := by
    rintro τ l' ⟨hlkτ, hiτ, m, b', hm, hjτ, hcs', hM', hfr⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "j") (eb := .const (BitVec.ofNat 32 num_proc)) hjτ rfl (by omega) hnp] at hg
    have hmlt : m < num_proc := by
      by_cases h : m < num_proc
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    obtain ⟨τ2, l2, b2, d2, hr2, hcs2, hM2, hlk2, hf2, hq, hτ2⟩ :=
      clear_triple εR c i0 hL "i" "j" (by decide) (by decide) x m τ l' b' (Ds d (rowS x m sp))
        (by rw [hlkτ]; exact hlk) hcs' hM' ⟨hiτ, hjτ, _, clear_step hpg hipt hx hmlt _⟩
    rw [clear_step hpg hipt hx hmlt] at hq
    simp only [Option.some.injEq] at hq
    rw [← hq] at hM2
    have h3 := asg_run (εR := εR) (c := c) (σ := τ2) (l := l2) "j" (.bin .add (.var "j") (.const 1))
      (inc_eval (m := m) (by rw [hτ2, Locals.set_other _ _ (by decide)]; exact hjτ))
    refine ⟨_, l2, Runs.seq hr2 h3, ⟨?_, ?_, m + 1, b2, hmlt, by simp, hcs2, hM2, fun k hk => ?_⟩, ?_⟩
    · simp [Locals.set, hlk2, hlkτ]
    · rw [Locals.set_other _ _ (by decide), hτ2, Locals.set_other _ _ (by decide)]; exact hiτ
    · rw [hf2 k hk, hfr k hk]
    · rw [Locals.set_same, hjτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨hlk', hi', m, b', hm, hj', hcs', hM', hfr⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) Inv (fun τ => num_proc - (τ "j").toNat) hbody num_proc σ l (by omega)
      ⟨rfl, hi, 0, b, by omega, hj, hcs, hM, fun _ _ => rfl⟩
  rw [ltu_eval (σ := σ') (ea := .var "j") (eb := .const (BitVec.ofNat 32 num_proc)) hj' rfl (by omega) hnp] at h0
  have hme : m = num_proc := by
    by_cases h : m < num_proc
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', l', b', hr, hcs', hM', hlk', hi'.trans hi.symm, hfr⟩

/-- **The loops of `shared_mem_init` clear the whole table**, through
`clear_shared_mem`'s specification. -/
theorem smInit_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (hnp0 : 0 < num_proc) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun _ d => d.pg = true ∧ d.ipt = true)
      (smInitLoop sb num_proc)
      (fun _ d _ d' => d' = { d with smspool := real_smspool num_proc d.smspool }) := by
  rintro σ l b d hlk hcs hM ⟨hpg, hipt⟩
  have hnp : num_proc < 2 ^ 32 := by
    have := hL.hse; have := hL.lay.hib; have := hL.lay.hfb; have := hL.lay.hend
    have := Nat.le_mul_self num_proc
    omega
  let σ0 := σ.set "i" 0
  have h0r : Runs (rprimsA εR c) (.assign "i" (.const 0)) σ l σ0 l := Runs.assign _ _
  let Inv : Locals → RLog → Prop := fun τ l' => τ "lk" = σ "lk" ∧ ∃ x b', x ≤ num_proc ∧
    τ "i" = BitVec.ofNat 32 x ∧ CS1 c i0 l' b' ∧
    MatchS maxpage num_id cb num_proc pb ib fb ida sb (Ds d (allS num_proc x d.smspool)) b' ∧
    ∀ k, ¬ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)) → b' k = b k
  have hbody : ∀ τ l', Inv τ l' → ¬ (Expr.bin .ltu (.var "i") (.const (BitVec.ofNat 32 num_proc))).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (smInitBody sb num_proc) τ l' τ' l'' ∧ Inv τ' l'' ∧
        num_proc - (τ' "i").toNat < num_proc - (τ "i").toNat := by
    rintro τ l' ⟨hlkτ, x, b', hx, hiτ, hcs', hM', hfr⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .const (BitVec.ofNat 32 num_proc)) hiτ rfl (by omega) hnp] at hg
    have hxlt : x < num_proc := by
      by_cases h : x < num_proc
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    let τ1 := τ.set "j" 0
    have h1 : Runs (rprimsA εR c) (.assign "j" (.const 0)) τ l' τ1 l' := Runs.assign _ _
    obtain ⟨τ3, l3, b3, hr3, hcs3, hM3, hlk3, hi3, hf3⟩ := smInitInner_run εR c i0 hL hpg hipt hxlt
      (allS num_proc x d.smspool) τ1 l' b' (by simp [τ1, Locals.set, hlkτ, hlk]) hcs' hM'
      (by simp [τ1, Locals.set, hiτ]) (by simp [τ1])
    have hiτ3 : τ3 "i" = BitVec.ofNat 32 x := by rw [hi3]; simp [τ1, Locals.set, hiτ]
    have h4 := asg_run (εR := εR) (c := c) (σ := τ3) (l := l3) "i" (.bin .add (.var "i") (.const 1))
      (inc_eval (m := x) hiτ3)
    refine ⟨_, l3, Runs.seq h1 (Runs.seq hr3 h4), ⟨?_, x + 1, b3, hxlt, by simp, hcs3, hM3, fun k hk => ?_⟩, ?_⟩
    · simp [Locals.set, hlk3, τ1, hlkτ]
    · rw [hf3 k hk, hfr k hk]
    · rw [Locals.set_same, hiτ, tn (show x + 1 < 2 ^ 32 by omega), tn (show x < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨hlk', x, b', hx, hi', hcs', hM', hfr⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) Inv (fun τ => num_proc - (τ "i").toNat) hbody num_proc σ0 l
      (by omega) ⟨by simp [σ0, Locals.set], 0, b, by omega, by simp [σ0], hcs, hM, fun _ _ => rfl⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .const (BitVec.ofNat 32 num_proc)) hi' rfl (by omega) hnp] at h0
  have hme : x = num_proc := by
    by_cases h : x < num_proc
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  rw [← allS_real hnp0] at hM'
  exact ⟨σ', l', b', _, Runs.seq h0r hr, hcs', hM', hlk', hfr, rfl⟩

end Init

end MShare
