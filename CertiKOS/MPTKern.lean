import CertiKOS.MPTCommon

/-!
# mCertiKOS `MPTKern`: mapping and unmapping a page, ported

`pt_insert` and `pt_rmv` (`mcertikos/mm/MPTCommonCSource.v`): map a physical
page at a virtual address, allocating the second-level table if needed, and
unmap one. Both keep the page's reference count in the allocation table.

Ported from `objects/ObjVMMFun.v`: `ptInsertPTE_spec`, `ptInsert_spec`,
`ptRmv_spec`, and `pt_Arg` from `layerlib/AuxStateDataType.v`.

Ported from `mm/MPTCommonCSource.v`: `pt_insert`, `pt_rmv`.

Not ported: `pt_init_kern` (boot, stage 2).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MPTKern

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon

/-! ## The count accessors in the state with page tables -/

section Lift
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

theorem set_at_c_pperm {d pd : PData} {i n : Nat} (h : set_at_c_spec maxpage i n d = some pd) :
    pd.pperm = d.pperm := by
  unfold set_at_c_spec at h
  by_cases hi : i < maxpage
  · rw [if_pos hi] at h
    cases hA : d.AT i with
    | ATUndef => rw [hA] at h; cases h
    | ATValid b0 t c0 =>
      rw [hA] at h
      cases t with
      | ATKern => cases h
      | ATResv => cases h
      | ATNorm => simp only [Option.some.injEq] at h; rw [← h]
  · rw [if_neg hi] at h; cases h

/-- **`at_get_c` in the state with page tables.** -/
theorem atGetC_lift (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (x : Ident) (hx : x ≠ "lk") (ie : Expr) (i : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 i ∧ ∃ v, get_at_c_spec maxpage i d.toPData = some v)
      (atGetCS x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_at_c_spec maxpage i d.toPData = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine (((atGetC_triple εR c i0 (num_id := num_id) (cb := cb) hmax x hx ie i).lift (π := PTData.toRData)
    (put := fun (d' : PTData) (r1 : RData) => ({ d' with toRData := r1 } : PTData))
    (M2 := MatchPT num_proc pb ib fb ida) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.mm, h.pt⟩, fun h => ⟨h.1, h.2⟩⟩)).conseq (fun _ _ h => h) ?_
  · intro d' b σ σ' d1 b' h2 hM hP hQ hf
    obtain ⟨he, -⟩ := hQ
    subst he
    exact matchpt_transfer hL h2 (fun k _ => hf k id) rfl rfl rfl (fun _ _ _ _ => rfl)
  · intro σ d σ' d'' _ hq
    obtain ⟨d1, he, hd1, v, hs, hσ⟩ := hq
    exact ⟨by rw [he, hd1], v, hs, hσ⟩

/-- **`at_set_c` in the state with page tables.** -/
theorem atSetC_lift (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (ie ve : Expr) (i n : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => k ≤ 3 * maxpage)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 i ∧ ve.eval σ = BitVec.ofNat 32 n ∧ n < 2 ^ 32 ∧
        ∃ pd, set_at_c_spec maxpage i n d.toPData = some pd)
      (atSetCS ie ve)
      (fun σ d σ' d' => ∃ r1 : RData, d' = { d with toRData := r1 } ∧
        ((∃ pd, set_at_c_spec maxpage i n d.toPData = some pd ∧ r1 = ⟨pd, d.AC⟩) ∧ σ' = σ.set "_" 0)) := by
  have := hL.hcb; have := hL.hpb
  refine ((atSetC_triple εR c i0 (num_id := num_id) hmax hL.hcb ie ve i n).lift (π := PTData.toRData)
    (put := fun (d' : PTData) (r1 : RData) => ({ d' with toRData := r1 } : PTData))
    (M2 := MatchPT num_proc pb ib fb ida) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.mm, h.pt⟩, fun h => ⟨h.1, h.2⟩⟩)
  intro d' b σ σ' d1 b' h2 hM hP hQ hf
  obtain ⟨⟨pd, hs, he⟩, -⟩ := hQ
  subst he
  refine matchpt_transfer hL h2 (fun k hk => hf k (by omega)) rfl rfl rfl (fun pi n i hh => ?_)
  show pd.pperm pi = d'.pperm pi
  rw [set_at_c_pperm hs]

end Lift

/-! ## Specifications (`ObjVMMFun.v`) -/

/-- `pt_Arg`. -/
def pt_Arg (num_proc n vadr padr np : Nat) : Prop := pt_Arg' num_proc n vadr ∧ 0 < padr ∧ padr < np

instance (num_proc n vadr padr np : Nat) : Decidable (pt_Arg num_proc n vadr padr np) := by
  unfold pt_Arg; exact inferInstance

/-- **`ptInsertPTE_spec`**: write the entry and count one more mapping of the page. -/
def ptInsertPTE_spec (nn vadr padr : Nat) (p : PTPerm) (d : PTData) : Option PTData :=
  if d.init = true then
    if nn = d.PT then none
    else
      match d.ptpool nn (PDX vadr) with
      | .PDEValid pi pdt =>
        if 0 < pi ∧ pi < 2 ^ 32 - 1 then
          match d.AT padr with
          | .ATValid true .ATNorm c =>
            if c < 2 ^ 32 - 1 then
              let pt' := setAt (d.ptpool nn) (PDX vadr) (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p)))
              some { d with AT := setAt d.AT padr (.ATValid true .ATNorm (c + 1)),
                            ptpool := setAt d.ptpool nn pt' }
            else none
          | _ => none
        else none
      | _ => none
  else none

/-- **`ptInsert_spec`**: map page `padr` at `vadr` in page table `nn`. Returns 0
if the second-level table was there, the page allocated for it if not, or
`MagicNumber` (`maxpage + 1`) if none could be allocated. -/
def ptInsert_spec (maxpage num_proc : Nat) (nn vadr padr perm : Nat) (d : PTData) : Option (PTData × Nat) :=
  if d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg num_proc nn vadr padr d.nps then
    match ZtoPerm perm with
    | some p =>
      match d.ptpool nn (PDX vadr) with
      | .PDEValid _ _ =>
        match ptInsertPTE_spec nn vadr padr p d with
        | some d' => some (d', 0)
        | none => none
      | .PDEUnPresent =>
        match ptAllocPDE_spec num_proc nn vadr d with
        | some (d', v) =>
          if v = 0 then some (d', maxpage + 1)
          else
            match ptInsertPTE_spec nn vadr padr p d' with
            | some d'' => some (d'', v)
            | none => none
        | none => none
      | _ => none
    | none => none
  else none

/-- **`ptRmv_spec`**: unmap `vadr` and count one mapping fewer. Returns the page
that was mapped, or 0. -/
def ptRmv_spec (maxpage num_proc : Nat) (n vadr : Nat) (d : PTData) : Option (PTData × Nat) :=
  if d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg' num_proc n vadr then
    if n = d.PT then none
    else
      match d.ptpool n (PDX vadr) with
      | .PDEValid pi pdt =>
        match pdt (PTX vadr) with
        | .PTEValid padr _ =>
          if 0 < padr ∧ padr < maxpage then
            match d.AT padr with
            | .ATValid true .ATNorm c =>
              if 0 < c ∧ c ≤ 2 ^ 32 - 1 then
                let pt' := setAt (d.ptpool n) (PDX vadr) (.PDEValid pi (setAt pdt (PTX vadr) .PTEUnPresent))
                some ({ d with AT := setAt d.AT padr (.ATValid true .ATNorm (c - 1)),
                               ptpool := setAt d.ptpool n pt' }, padr)
              else none
            | _ => none
          else none
        | .PTEUnPresent => some (d, 0)
        | .PTEUndef => none
      | _ => none
  else none

end MPTKern
