import CertiKOS.TDispatch

/-!
# mCertiKOS `TTrap`: the shared-memory system call, ported

Ported from `objects/ObjTrap.v`: `trap_offer_shared_mem_spec` (`SYS_share`,
number 27). Process 1 offers the page at argument 2 to process 2, through
`offer_shared_mem` (`MShare.lean`); the answer is the return value. Any other
caller gets `E_SUCC` and nothing happens.

* `liftSC`: **a triple of the shared-memory layer holds in the state with
  threads, queues and the current thread**, if it writes only the cells of
  the layers below and keeps `pg`. (`liftPC` does this for the page-table
  layers.)
* `offer_flags`: `offer_shared_mem_spec` keeps the paging flags.
* `trapShare_triple`: **`sys_offer_shared_mem` refines
  `trap_offer_shared_mem_spec`.** `offer_shared_mem` is called through
  `offer_triple`, carried up by `liftSC`, `liftCI` and `liftIU`.

The C code is not in the public sources (the dispatcher's specification calls
`trap_offer_shared_mem_spec`, which is a specification only). It is written
here from the specification:
```
void sys_offer_shared_mem(void) {
  vadr = uctx_arg2();
  if (get_curid() == 1) { r = offer_shared_mem(1, 2, vadr); uctx_set_retval1(r); }
  uctx_set_errno(E_SUCC);
}
```
What differs: the handler assumes the invariants of the memory manager
(`ATInv`, `UQ`) that mCertiKOS keeps as layer invariants.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TTrap

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc FlatMem
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Specification (`ObjTrap.v`) -/

def SYS_share : Nat := 27

/-- **`trap_offer_shared_mem_spec`**: process 1 offers the page at argument 2
to process 2. -/
def trap_offer_shared_mem_spec (num_proc maxpage : Nat) (d : UData) : Option UData :=
  match uctx_arg2_spec d with
  | some vadr =>
    if d.cid = 1 then
      match offer_shared_mem_spec num_proc maxpage 1 2 vadr d.toSData with
      | some (s', res) =>
        match uctx_set_retval1_spec res { d with toSData := s' } with
        | some d1 => uctx_set_errno_spec E_SUCC d1
        | none => none
      | none => none
    else uctx_set_errno_spec E_SUCC d
  | none => none

/-! ## The code -/

/-- `sys_offer_shared_mem`. -/
def trapShareS (cb maxpage pb fb sb num_proc cidb ucb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "sva" U_EBX)
    (.ite (.bin .eq (.var "curid") (.const 1))
      (.seq (.assign "pid1" (.const 1)) (.seq (.assign "pid2" (.const 2))
        (.seq (offerS cb maxpage pb fb sb num_proc) (retDoneS cidb ucb (.var "r")))))
      (uctxSetRegS cidb ucb U_EAX (.const 0)))

/-- The cells the shared-memory layer may write: the layers below and the
table. -/
def ShareF (cb num_id pb sb num_proc : Nat) (k : Nat) : Prop :=
  (k < cb + 5 * num_id ∨ pb ≤ k) ∨ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))

/-- `offer_shared_mem_spec` keeps the paging flags. -/
theorem offer_flags {num_proc maxpage p1 p2 va : Nat} {d d' : SData} {r : Nat}
    (h : offer_shared_mem_spec num_proc maxpage p1 p2 va d = some (d', r)) : d'.pg = d.pg := by
  unfold offer_shared_mem_spec at h
  repeat' (split at h)
  all_goals first
    | (cases h; rfl)
    | (cases h; rename_i hR _; exact (ptResv2_flags hR).1)
    | cases h

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb
local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb

/-- **Passthrough for the shared-memory layer.** -/
theorem liftSC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    {P : Locals → SData → Prop} {s : Stmt APrim} {Q : Locals → SData → Locals → SData → Prop} {F : Nat → Prop}
    (h : Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb) F P s Q)
    (hF : ∀ k, F k → ShareF cb num_id pb sb num_proc k)
    (hpg : ∀ σ d σ' d', P σ d → Q σ d σ' d' → d'.pg = d.pg) :
    Triple εR c i0 MC F (fun σ d => P σ d.toSData) s
      (fun σ d σ' d' => ∃ p : SData, d' = { d with toSData := p } ∧ Q σ d.toSData σ' p) := by
  intro σ l b d hlk hcs ⟨⟨q, hQ, hS, hR, hInv⟩, hcid⟩ hp
  have hSL := hL.qlay.tlay.slay
  have := hSL.hsb; have := hSL.hse; have := hL.qlay.tlay.htb; have := hL.qlay.tlay.hte
  have := hL.qlay.hqb; have := hL.qlay.hqe; have := hL.hcb; have := hL.hce
  have hp' : P σ q.toSData := hS ▸ hp
  obtain ⟨σ', l', b', p, hr, hcs', hA', hlk', hf, hq⟩ := h σ l b q.toSData hlk hcs hQ.t.s hp'
  have hgap : ∀ k, tb ≤ k → k < pb → b' k = b k := fun k h1 h2 =>
    hf k (fun hk => by have := hF k hk; unfold ShareF at this; omega)
  have hq' : Q σ d.toSData σ' p := by rw [hS]; exact hq
  refine ⟨σ', l', b', { d with toSData := p }, hr, hcs',
    ⟨⟨({ q with toSData := p } : QData), ⟨⟨hA', fun j hj => ?_⟩, fun j hj => ?_⟩,
      rfl, hR, fun hpg' => hInv ?_⟩, ?_⟩, hlk', hf, p, rfl, hq'⟩
  · show MatchTCB (q.tcb j) _ _ _
    rw [hgap _ (by unfold tcell; omega) (by unfold tcell; omega),
      hgap _ (by unfold tcell; omega) (by unfold tcell; omega),
      hgap _ (by unfold tcell; omega) (by unfold tcell; omega)]
    exact hQ.t.tp j hj
  · show MatchTDQ (q.tdq j) _ _
    rw [hgap _ (by unfold qcell; omega) (by unfold qcell; omega),
      hgap _ (by unfold qcell; omega) (by unfold qcell; omega)]
    exact hQ.qp j hj
  · have e := hpg σ q.toSData σ' p hp' hq
    show q.toSData.pg = true
    rw [← e]; exact hpg'
  · show d.cid = (b' cidb).toNat
    rw [hgap cidb (by omega) (by omega)]; exact hcid

/-- **`sys_offer_shared_mem` refines `trap_offer_shared_mem_spec`.** -/
theorem trapShare_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} :
    Triple εR c i0 MU (fun k => ShareF cb num_id pb sb num_proc k ∨ UCF ucb num_proc k)
      (fun _ d => d.cid < num_proc ∧ ATInv maxpage kl kh d.toPData ∧ UQ d.AC ∧
        ∃ d1, trap_offer_shared_mem_spec num_proc maxpage d = some d1)
      (trapShareS cb maxpage pb fb sb num_proc cidb ucb)
      (fun _ d _ d' => trap_offer_shared_mem_spec num_proc maxpage d = some d') := by
  intro σ l b d hlk hcs hM ⟨hcp, hAT, hUQ, d', hs⟩
  have hCL := hL.ilay.clay
  have hLay := hCL.qlay.tlay.slay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hL.ilay.hie; have := hCL.hcb
  have := hCL.hce; have := hCL.qlay.hqb; have := hCL.qlay.hqe; have := hCL.qlay.tlay.htb
  have := hCL.qlay.tlay.hte; have := hLay.hsb; have := hLay.hse
  have hs0 := hs
  unfold trap_offer_shared_mem_spec at hs
  cases e2 : uctx_arg2_spec d with
  | none => rw [e2] at hs; cases hs
  | some va =>
    rw [e2] at hs
    simp only at hs
    obtain ⟨hva, hva32⟩ := arg_val e2
    -- `vadr = uctx_arg2();`
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (uctxArgU (ida := ida) (cidb := cidb) εR c i0 hL
      (F := fun _ => False) "sva" (by decide) (reg := U_EBX) (by decide) (σ := σ) hcp hva).2 l b hlk hcs hM
    have hb1 : b = b1 := (funext (fun k => f1 k (fun h => h))).symm
    subst hb1
    let σ1 := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "sva" (BitVec.ofNat 32 va)
    have hcur : σ1 "curid" = BitVec.ofNat 32 d.cid := by simp [σ1, Locals.set]
    have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
    by_cases h1 : d.cid = 1
    · rw [if_pos h1] at hs
      cases ho : offer_shared_mem_spec num_proc maxpage 1 2 va d.toSData with
      | none => rw [ho] at hs; cases hs
      | some pr =>
        obtain ⟨s', res⟩ := pr
        rw [ho] at hs
        simp only at hs
        cases hr1 : uctx_set_retval1_spec res { d with toSData := s' } with
        | none => rw [hr1] at hs; cases hs
        | some d2 =>
          rw [hr1] at hs
          simp only at hs
          let σ3 := (σ1.set "pid1" 1).set "pid2" 2
          have T := liftIU εR c i0 hL (liftCI εR c i0 hL.ilay (liftSC εR c i0 hCL
            ((offer_triple εR c i0 hLay hmax hnum hmp hnn (kl := kl) (kh := kh) (ida := ida) 1 2 va hva32).conseq
              (P' := fun σ (e : SData) => σ "pid1" = BitVec.ofNat 32 1 ∧ σ "pid2" = BitVec.ofNat 32 2 ∧
                σ "sva" = BitVec.ofNat 32 va ∧ ATInv maxpage kl kh e.toPData ∧ UQ e.AC ∧
                ∃ d1 r, offer_shared_mem_spec num_proc maxpage 1 2 va e = some (d1, r))
              (fun _ _ h => h) (fun _ _ _ _ _ h => h))
            (fun k hk => hk) (fun _ _ _ _ _ hq => by obtain ⟨r, hq, -⟩ := hq; exact offer_flags hq))
            (fun k hk => by omega)) (fun k hk => by omega)
          obtain ⟨σ4, l4, b4, u4, r4, c4, m4, k4, f4, i4, hu4, cc, hi4, p4, hcc, rr, hq4, hr4⟩ :=
            T σ3 l1 b d (by simpa [σ3, Locals.set] using hlk1) c1 m1
              ⟨by simp [σ3, Locals.set], by simp [σ3, Locals.set], by simp [σ3, σ1, Locals.set], hAT, hUQ,
                s', res, ho⟩
          rw [ho] at hq4
          simp only [Option.some.injEq, Prod.mk.injEq] at hq4
          obtain ⟨e1, e2'⟩ := hq4
          subst e1; subst e2'; subst hcc; subst hi4; subst hu4
          obtain ⟨σ5, hst5, hlk5⟩ := retDone_step (ida := ida) (cidb := cidb) εR c i0 hL
            (F := UCF ucb num_proc) (fun _ h => h) (ve := .var "r") (σ := σ4) (d := { d with toSData := s' }) (by show ((σ4.set "curid" _) "r") = _; rw [Locals.set_other _ _ (by decide)]; exact hr4)
            (by exact hcp) hr1 hs
          obtain ⟨l5, b5, r5, c5, m5, f5⟩ := hst5.2 l4 b4 (by rw [k4]; simpa [σ3, Locals.set] using hlk1) c4 m4
          refine ⟨σ5, l5, b5, d', Runs.seq r1 (Runs.ite_true (eqc_true (b := 1) hcur h1)
            (Runs.seq (asg_run "pid1" (.const 1) rfl) (Runs.seq (asg_run "pid2" (.const 2) rfl)
              (Runs.seq r4 r5)))), c5, m5, ?_, fun k hk => ?_, hs0⟩
          · rw [hlk5, k4]; simp [σ3, σ1, Locals.set]
          · rw [f5 k (fun h => hk (Or.inr h)), f4 k (fun h => hk (Or.inl h))]
    · rw [if_neg h1] at hs
      obtain ⟨l2, b2, r2, c2, m2, f2⟩ := (setReg_step (ida := ida) (cidb := cidb) εR c i0 hL
        (F := UCF ucb num_proc) (fun _ h => h) (reg := U_EAX) (by decide) (ve := .const 0) (σ := σ1)
        (n := E_SUCC) rfl hcp hs).2 l1 b hlk1 c1 m1
      refine ⟨_, l2, b2, d', Runs.seq r1 (Runs.ite_false (eqc_false (b := 1) hcur (by omega) (by decide) h1) r2),
        c2, m2, by simp [σ1, Locals.set], fun k hk => f2 k (fun h => hk (Or.inr h)), hs0⟩

end Code

end TTrap
