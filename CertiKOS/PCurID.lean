import CertiKOS.PAbQueueInv

/-!
# mCertiKOS `PCurID`: the current thread, ported

One more word of thread data: the id of the thread that is running.

Ported from `objects/ObjThread.v`: `get_curid_spec`, `set_curid_spec`.
Ported from `proc/CurIDGen.v`: `match_CurID` (in `MatchC`). Ported from
`proc/PAbQueueCSource.v`: the C code of `get_curid` and `set_curid`.

* `getCurid_triple`, `setCurid_triple`: both refine their specifications.
* `liftA`: every primitive of `PAbQueue` keeps its interface in the state
  with the current thread, if it does not write that word.

What differs: the word is a cell of the memory-management region, after the
queue pool (`CLayout`). The functions built on this layer in mCertiKOS
(`thread_spawn`, `sched_init`, `thread_wakeup`) belong to the scheduler and
are not in this file.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PCurID

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue
open MALInit (rd_run wr_run tn)

/-- `AData` with the current thread. -/
structure CData extends AData where
  cid : Nat

/-! ## Specifications (`ObjThread.v`) -/

def get_curid_spec (d : CData) : Option Nat :=
  if d.pg = true then some d.cid else none

def set_curid_spec (num_proc i : Nat) (d : CData) : Option CData :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_proc then some { d with cid := i } else none

/-! ## The word in the region (`CurIDGen.v`) -/

/-- The layout with the current-thread word after the queue pool. -/
structure CLayout (maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb : Nat) : Prop where
  qlay : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb
  hcb : qb + 2 * (num_chan + 1) ≤ cidb
  hce : cidb < pb

/-- `match_CurID` on top of the list view. -/
def MatchC (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb : Nat) (d : CData) (b : Region) :
    Prop :=
  MatchA maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb d.toAData b ∧ d.cid = (b cidb).toNat

section Region
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb : Nat}

/-- The queue layer and those below depend only on the cells up to the end of
the queue pool and from the page-table pool on. -/
theorem matchQ_frame (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {d : QData}
    {b b' : Region} (hM : MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb d b)
    (hfr : ∀ k, k < qb + 2 * (num_chan + 1) ∨ pb ≤ k → b' k = b k) :
    MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb d b' := by
  have := hL.hqb; have := hL.hqe
  refine ⟨matchT_frame hL.tlay hM.t (fun k hk => hfr k (by omega)), fun j hj => ?_⟩
  rw [hfr _ (Or.inl (by unfold qcell; omega)), hfr _ (Or.inl (by unfold qcell; omega))]
  exact hM.qp j hj

/-- So does the list view. -/
theorem matchA_frame (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {a : AData}
    {b b' : Region} (hM : MatchA maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb a b)
    (hfr : ∀ k, k < qb + 2 * (num_chan + 1) ∨ pb ≤ k → b' k = b k) :
    MatchA maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb a b' := by
  obtain ⟨q, hq, hR⟩ := hM
  exact ⟨q, matchQ_frame hL hq hfr, hR⟩

theorem cidb_lt (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) : cidb < 2 ^ 32 := by
  have := hL.hce; have := hL.qlay.tlay.slay.lay.hib; have := hL.qlay.tlay.slay.lay.hfb
  have := hL.qlay.tlay.slay.lay.hend; omega

end Region

/-! ## The C code (`PAbQueueCSource.v`) -/

/-- `x = get_curid()`: `return CURID_LOC;` -/
def getCuridS (cidb : Nat) (x : Ident) : Stmt APrim := .call x .pull [lkE, .const (BitVec.ofNat 32 cidb)]

/-- `set_curid(v)`: `CURID_LOC = v;` -/
def setCuridS (cidb : Nat) (ve : Expr) : Stmt APrim := .call "_" .push [lkE, .const (BitVec.ofNat 32 cidb), ve]

section Steps
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MA" => MatchA maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb
local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb

theorem getCuridC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) (x : Ident)
    (hx : x ≠ "lk") (σ : Locals) (d : CData) :
    Step εR c i0 MC F (getCuridS cidb x) σ d (σ.set x (BitVec.ofNat 32 d.cid)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (.const (BitVec.ofNat 32 cidb)) (n := cidb) (tn (cidb_lt hL))
  have e : b cidb = BitVec.ofNat 32 d.cid := val_of_toNat hM.2.symm (hM.2 ▸ (b cidb).isLt)
  rw [e] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem setCuridC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    (hF : ∀ k, k = cidb → F k) {ve : Expr} {σ : Locals} {d : CData} {i : Nat}
    (hve : ve.eval σ = BitVec.ofNat 32 i) (hi : i < 2 ^ 32) :
    Step εR c i0 MC F (setCuridS cidb ve) σ d (σ.set "_" 0) { d with cid := i } := by
  have := hL.hcb; have := hL.hce
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (.const (BitVec.ofNat 32 cidb)) ve (n := cidb)
    (tn (cidb_lt hL)) hve
  refine ⟨l', _, hr, hcs', ⟨matchA_frame hL.qlay hM.1 (fun k hk => sc_ne _ _ (by omega)), ?_⟩,
    fun k hk => sc_ne _ _ (fun e => hk (hF k e))⟩
  show i = (setCell b cidb (BitVec.ofNat 32 i) cidb).toNat
  rw [sc_eq, tn hi]

/-- **`get_curid` refines `get_curid_spec`.** -/
theorem getCurid_triple (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) (x : Ident)
    (hx : x ≠ "lk") :
    Triple εR c i0 MC (fun _ => False) (fun _ d => ∃ v, get_curid_spec d = some v) (getCuridS cidb x)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_curid_spec d = some v ∧ σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨v, hs⟩ => ?_)
  have hs0 := hs
  unfold get_curid_spec at hs
  by_cases hc : d.pg = true
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    exact ⟨_, d, getCuridC εR c i0 hL x hx σ d, rfl, _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`set_curid` refines `set_curid_spec`.** -/
theorem setCurid_triple (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) (ve : Expr)
    (i : Nat) :
    Triple εR c i0 MC (fun k => k = cidb)
      (fun σ d => ve.eval σ = BitVec.ofNat 32 i ∧ ∃ d1, set_curid_spec num_proc i d = some d1)
      (setCuridS cidb ve)
      (fun σ d σ' d' => set_curid_spec num_proc i d = some d' ∧ σ' = σ.set "_" 0) := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL.qlay
  refine Step.triple (fun σ d ⟨hve, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold set_curid_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ i < num_proc
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    exact ⟨_, _, setCuridC εR c i0 hL (fun _ h => h) hve (by omega), hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- **Every primitive of the list view keeps its interface in the state with
the current thread**, if it does not write that word. -/
theorem liftA (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    {P : Locals → AData → Prop} {s : Stmt APrim} {Q : Locals → AData → Locals → AData → Prop}
    (h : Triple εR c i0 MA F P s Q) (hF : ∀ k, F k → k ≠ cidb) :
    Triple εR c i0 MC F (fun σ d => P σ d.toAData) s
      (fun σ d σ' d' => ∃ a : AData, d' = { d with toAData := a } ∧ Q σ d.toAData σ' a) :=
  h.lift (π := CData.toAData) (put := fun (d' : CData) (a : AData) => ({ d' with toAData := a } : CData))
    (M2 := fun d' b => d'.cid = (b cidb).toNat) (fun _ _ => rfl)
    (fun d' b σ σ' d1 b' h2 hM hP hQ hf => by
      show d'.cid = (b' cidb).toNat
      rw [hf cidb (fun hk => hF _ hk rfl)]; exact h2)

end Steps

end PCurID
