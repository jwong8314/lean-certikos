import CertiKOS.MPTKern

/-!
# mCertiKOS `MPTInit`/`MPTNew`: reserving a page and creating a process's quota, ported

The top of the page-table code (`mcertikos/mm/MPTInitCSource.v`).

Ported from `objects/ObjLMM1.v`: `pt_new_spec`. Ported from
`objects/ObjLMM0.v`: `ptResv_spec`, in the form its C code is verified
against: `container_alloc_spec` followed by `ptInsert_spec`.

Ported from `mm/MPTInitCSource.v`: `pt_new`, `pt_resv`.

What is not here: mCertiKOS then abstracts the reference counts of the
allocation table into lists of owners (`LAT`, `ptInsert0_spec`,
`ptRmv0_spec`, `consistent_pmap`). That step is a refinement between two
abstract states, with no C code. It is not ported yet. Also not ported:
`pt_resv2` (shared memory, stage 3), `pmap_init` and `pt_init` (boot), and
`pt_free`, which the sources leave unused.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MPTNew

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern

/-! ## `pt_new` -/

/-- **`pt_new_spec`**: give `q` pages of process `id`'s quota to a new child. -/
def pt_new_spec (num_id mc : Nat) (id q : Nat) (d : PTData) : Option (PTData × Nat) :=
  if d.pg = true ∧ d.ipt = true then
    match container_split_spec num_id mc id q d.toRData with
    | some (r1, i) => some ({ d with toRData := r1 }, i)
    | none => none
  else none

section New
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

theorem split_pperm {mc id q r : Nat} {d d1 : RData} (h : container_split_spec num_id mc id q d = some (d1, r)) :
    d1.pperm = d.pperm := by
  unfold container_split_spec at h
  simp only at h
  by_cases hc : (d.AC id).cused = true ∧ id * mc + 1 + (d.AC id).cchildren.length < num_id ∧
      (d.AC id).cchildren.length < mc ∧ q + (d.AC id).cusage ≤ (d.AC id).cquota
  · rw [if_pos hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
  · rw [if_neg hc] at h; cases h

/-- **`container_split` in the state with page tables.** -/
theorem container_split_lift (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : Layout maxpage num_id cb num_proc pb ib fb) (hnum : cb + 5 * num_id < 2 ^ 32)
    (mc id q : Nat) (hid : id < num_id) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => cb ≤ k ∧ k < cb + 5 * num_id)
      (fun σ d => σ "id" = BitVec.ofNat 32 id ∧ σ "amt" = BitVec.ofNat 32 q ∧
        ∃ d1 r, container_split_spec num_id mc id q d.toRData = some (d1, r))
      (ctSplitCS cb (BitVec.ofNat 32 mc))
      (fun _ d σ' d' => ∃ r1 : RData, d' = { d with toRData := r1 } ∧
        ∃ r, container_split_spec num_id mc id q d.toRData = some (r1, r) ∧ σ' "r" = BitVec.ofNat 32 r) := by
  have := hL.hcb; have := hL.hpb
  refine ((container_split_triple εR c i0 (maxpage := maxpage) hL.hcb hnum mc id q hid).lift
    (π := PTData.toRData)
    (put := fun (d' : PTData) (r1 : RData) => ({ d' with toRData := r1 } : PTData))
    (M2 := MatchPT num_proc pb ib fb ida) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.mm, h.pt⟩, fun h => ⟨h.1, h.2⟩⟩)
  intro d' b σ σ' d1 b' h2 hM hP hQ hf
  obtain ⟨r, hs, -⟩ := hQ
  refine matchpt_transfer hL h2 (fun k hk => hf k (by omega)) rfl rfl rfl (fun pi n i hh => ?_)
  show d1.pperm pi = d'.pperm pi
  rw [split_pperm hs]

/-- `pt_new(id, quota)`: `return container_split(id, quota);` -/
def ptNewS (cb mc : Nat) : Stmt APrim := ctSplitCS cb (BitVec.ofNat 32 mc)

/-- **`pt_new` refines `pt_new_spec`.** -/
theorem ptNew_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hnum : cb + 5 * num_id < 2 ^ 32) (mc id q : Nat) (hid : id < num_id) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => cb ≤ k ∧ k < cb + 5 * num_id)
      (fun σ d => σ "id" = BitVec.ofNat 32 id ∧ σ "amt" = BitVec.ofNat 32 q ∧
        ∃ d1 r, pt_new_spec num_id mc id q d = some (d1, r))
      (ptNewS cb mc)
      (fun _ d σ' d' => ∃ r, pt_new_spec num_id mc id q d = some (d', r) ∧ σ' "r" = BitVec.ofNat 32 r) := by
  refine (container_split_lift εR c i0 hL hnum mc id q hid).conseq ?_ ?_
  · intro σ d ⟨h1, h2, d1, r, hs⟩
    refine ⟨h1, h2, ?_⟩
    unfold pt_new_spec at hs
    by_cases hc : d.pg = true ∧ d.ipt = true
    · rw [if_pos hc] at hs
      cases hsp : container_split_spec num_id mc id q d.toRData with
      | none => rw [hsp] at hs; cases hs
      | some pr => exact ⟨pr.1, pr.2, rfl⟩
    · rw [if_neg hc] at hs; cases hs
  · intro σ d σ' d' ⟨_, _, d1, r, hs⟩ ⟨r1, hd', r', hsp, hr⟩
    refine ⟨r', ?_, hr⟩
    unfold pt_new_spec at hs ⊢
    by_cases hc : d.pg = true ∧ d.ipt = true
    · rw [if_pos hc, hsp, hd']
    · rw [if_neg hc] at hs; cases hs

end New

end MPTNew
