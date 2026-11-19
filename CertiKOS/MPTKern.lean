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

/-! ## Writing the entry and counting the mapping -/

/-- `pt_insert_aux(n, vadr, padr, perm); count = at_get_c(padr); at_set_c(padr, count + 1);` -/
def insTailS (pb fb : Nat) : Stmt APrim :=
  .seq (ptInsertAuxS pb fb) (.seq (atGetCS "count" (.var "padr"))
    (atSetCS (.var "padr") (.bin .add (.var "count") (.const 1))))

section Tail
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- The tail of `pt_insert` refines `ptInsertPTE_spec`, through the
specifications of `pt_insert_aux`, `at_get_c` and `at_set_c`. -/
theorem insTail_run (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) {σ : Locals} {l : RLog} {b : Region}
    {d d' : PTData} (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b)
    (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida d b) {nn vadr padr perm : Nat} {p : PTPerm}
    (hn : σ "n" = BitVec.ofNat 32 nn) (hva : σ "vaddr" = BitVec.ofNat 32 vadr)
    (hpa : σ "padr" = BitVec.ofNat 32 padr) (hpe : σ "perm" = BitVec.ofNat 32 perm)
    (hipt : d.ipt = true) (hnp : nn < num_proc) (hv : vadr < 2 ^ 32) (hz : ZtoPerm perm = some p)
    (hpr : 0 < padr ∧ padr < d.nps) (hnps : d.nps ≤ maxpage)
    (hs : ptInsertPTE_spec nn vadr padr p d = some d') :
    ∃ σ' l' b', Runs (rprimsA εR c) (insTailS pb fb) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MatchAll maxpage num_id cb num_proc pb ib fb ida d' b' ∧ σ' "lk" = σ "lk" ∧
      ∀ z : Ident, z ≠ "i" → z ≠ "vadr" → z ≠ "o" → z ≠ "_" → z ≠ "count" → σ' z = σ z := by
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb; have := hL.hcb
  have hpdx : PDX vadr < 1024 := by unfold PDX; omega
  have hptx : PTX vadr < 1024 := by unfold PTX; omega
  unfold ptInsertPTE_spec at hs
  have hinit : d.init = true := by
    by_cases h : d.init = true
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hinit] at hs
  have hPT : ¬ nn = d.PT := by
    intro h; rw [if_pos h] at hs; cases hs
  rw [if_neg hPT] at hs
  cases hp : d.ptpool nn (PDX vadr) with
  | PDEID => rw [hp] at hs; cases hs
  | PDEUnPresent => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEValid pi pdt =>
    rw [hp] at hs; simp only at hs
    have hpi : 0 < pi ∧ pi < 2 ^ 32 - 1 := by
      by_cases h : 0 < pi ∧ pi < 2 ^ 32 - 1
      · exact h
      · rw [if_neg h] at hs; cases hs
    rw [if_pos hpi] at hs
    cases hA : d.AT padr with
    | ATUndef => rw [hA] at hs; cases hs
    | ATValid b0 t cnt =>
      rw [hA] at hs
      cases b0 <;> cases t <;> simp only at hs <;> try (cases hs)
      have hcl : cnt < 2 ^ 32 - 1 := by
        by_cases h : cnt < 2 ^ 32 - 1
        · exact h
        · rw [if_neg h] at hs; cases hs
      rw [if_pos hcl] at hs
      simp only [Option.some.injEq] at hs
      -- pt_insert_aux
      have e1 : ptInsertAux_spec num_proc nn vadr padr perm d = some { d with
          ptpool := setAt d.ptpool nn (setAt (d.ptpool nn) (PDX vadr)
            (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p)))) } := by
        unfold ptInsertAux_spec setPTE_spec
        rw [if_pos ⟨hinit, hipt, ⟨hnp, hpdx⟩, hptx⟩, hz]
        simp only
        rw [if_neg hPT, if_pos hpr, hp]
      obtain ⟨σ1, l1, b1, d1, hr1, hcs1, hM1, hlk1, -, hq1⟩ :=
        ptInsertAux_triple εR c i0 hL nn vadr padr perm hv σ l b d hlk hcs hM
          ⟨hn, hva, hpa, hpe, Nat.le_trans hnps hmp, _, e1⟩
      rw [e1] at hq1; simp only [Option.some.injEq] at hq1
      rw [← hq1] at hM1
      have hpa1 : σ1 "padr" = BitVec.ofNat 32 padr := by
        rw [hr1.frame (by simp [frS, ptInsertAuxS, withPDXPTX, setPTES, pteStoreS])]; exact hpa
      -- count = at_get_c(padr)
      have e2 : get_at_c_spec maxpage padr (PTData.toRData { d with
          ptpool := setAt d.ptpool nn (setAt (d.ptpool nn) (PDX vadr)
            (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p)))) }).toPData = some cnt := by
        unfold get_at_c_spec
        rw [if_pos (by omega)]
        show (match d.AT padr with
          | .ATValid _ _ n => some n
          | .ATUndef => none) = some cnt
        rw [hA]
      obtain ⟨σ2, l2, b2, d2, hr2, hcs2, hM2, hlk2, -, hd2, v, hsv, hσ2⟩ :=
        atGetC_lift εR c i0 hL hmax "count" (by decide) (.var "padr") padr σ1 l1 b1 _
          (by rw [hlk1]; exact hlk) hcs1 hM1 ⟨hpa1, _, e2⟩
      rw [e2] at hsv; simp only [Option.some.injEq] at hsv
      rw [hd2] at hM2
      -- at_set_c(padr, count + 1)
      have e3 : set_at_c_spec maxpage padr (cnt + 1) (PTData.toRData { d with
          ptpool := setAt d.ptpool nn (setAt (d.ptpool nn) (PDX vadr)
            (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p)))) }).toPData =
          some { d.toPData with AT := setAt d.AT padr (.ATValid true .ATNorm (cnt + 1)) } := by
        unfold set_at_c_spec
        rw [if_pos (by omega)]
        show (match d.AT padr with
          | .ATValid b .ATNorm _ => some { d.toPData with AT := setAt d.AT padr (.ATValid b .ATNorm (cnt + 1)) }
          | _ => none) = _
        rw [hA]
      obtain ⟨σ3, l3, b3, d3, hr3, hcs3, hM3, hlk3, -, r1, hd3, ⟨pd, hpd, hr1e⟩, -⟩ :=
        atSetC_lift εR c i0 hL hmax (.var "padr") (.bin .add (.var "count") (.const 1)) padr (cnt + 1)
          σ2 l2 b2 _ (by rw [hlk2, hlk1]; exact hlk) hcs2 hM2
          ⟨by show σ2 "padr" = _; rw [hσ2, Locals.set_other _ _ (by decide)]; exact hpa1,
           by show σ2 "count" + 1 = _; rw [hσ2, Locals.set_same, ← hsv]; simp [BitVec.ofNat_add],
           by omega, _, e3⟩
      rw [e3] at hpd; simp only [Option.some.injEq] at hpd
      rw [hd3, hr1e, ← hpd] at hM3
      refine ⟨σ3, l3, b3, Runs.seq hr1 (Runs.seq hr2 hr3), hcs3, ?_, by rw [hlk3, hlk2, hlk1],
        fun z h1 h2 h3 h4 h5 => (Runs.seq hr1 (Runs.seq hr2 hr3)).frame (by
          simp [frS, insTailS, ptInsertAuxS, withPDXPTX, setPTES, pteStoreS, atGetCS, atSetCS, Ne.symm h1,
            Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5])⟩
      rw [← hs]; exact hM3

end Tail

/-! ## `pt_insert` -/

theorem insertPTE_pi_pos {nn vadr padr : Nat} {p : PTPerm} {d d' : PTData} {pi : Nat} {pdt : PTE}
    (h : ptInsertPTE_spec nn vadr padr p d = some d') (hp : d.ptpool nn (PDX vadr) = .PDEValid pi pdt) :
    0 < pi ∧ pi < 2 ^ 32 - 1 := by
  unfold ptInsertPTE_spec at h
  by_cases hin : d.init = true
  · rw [if_pos hin] at h
    by_cases hPT : nn = d.PT
    · rw [if_pos hPT] at h; cases h
    · rw [if_neg hPT, hp] at h
      simp only at h
      by_cases hpi : 0 < pi ∧ pi < 2 ^ 32 - 1
      · exact hpi
      · rw [if_neg hpi] at h; cases h
  · rw [if_neg hin] at h; cases h

theorem allocPDE_facts {num_proc nn vadr : Nat} {d d2 : PTData} {v : Nat}
    (h : ptAllocPDE_spec num_proc nn vadr d = some (d2, v)) :
    d2.nps = d.nps ∧ d2.ipt = d.ipt ∧ (v = 0 ∨ (0 < v ∧ v < d.nps)) := by
  unfold ptAllocPDE_spec at h
  simp only at h
  by_cases hc : d.init = true ∧ d.ipt = true ∧ (d.AC nn).cused = true ∧ pt_Arg' num_proc nn vadr
  · rw [if_pos hc] at h
    by_cases hPT : nn = d.PT
    · rw [if_pos hPT] at h; cases h
    · rw [if_neg hPT] at h
      cases hp : d.ptpool nn (PDX vadr) with
      | PDEValid pi pdt => rw [hp] at h; cases h
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
      | PDEUnPresent =>
        rw [hp] at h; simp only at h
        by_cases hlt : (d.AC nn).cusage < (d.AC nn).cquota
        · rw [if_pos hlt] at h
          cases hff : first_free d.AT d.nps with
          | none => rw [hff] at h; cases h
          | some p =>
            rw [hff] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            obtain ⟨h0, hn, -, -⟩ := first_free_some hff
            exact ⟨rfl, rfl, Or.inr ⟨h0, hn⟩⟩
        · rw [if_neg hlt] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, rfl, Or.inl rfl⟩
  · rw [if_neg hc] at h; cases h

/-- ```
pi = pt_read_pde(n, vadr);
if (pi != 0) result = 0;
else { result = pt_alloc_pde(n, vadr); if (result == 0) result = MagicNumber; }
if (result != MagicNumber) {
  pt_insert_aux(n, vadr, padr, perm);
  count = at_get_c(padr); at_set_c(padr, count + 1);
}
return result;
``` -/
def ptInsertS (cb maxpage pb fb : Nat) : Stmt APrim :=
  .seq (ptReadPDES pb)
  (.seq (.ite (.bin .ne (.var "r") (.const 0)) (.assign "res" (.const 0))
      (.seq (ptAllocPDES cb maxpage pb fb) (.seq (.assign "res" (.var "r"))
        (.ite (.bin .eq (.var "res") (.const 0))
          (.assign "res" (.const (BitVec.ofNat 32 (maxpage + 1)))) .skip))))
  (.seq (.ite (.bin .ne (.var "res") (.const (BitVec.ofNat 32 (maxpage + 1)))) (insTailS pb fb) .skip)
    (.assign "r" (.var "res"))))

section Insert
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **`pt_insert` refines `ptInsert_spec`.** -/
theorem ptInsert_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (nn vadr padr perm : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => True)
      (fun σ d => σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        σ "padr" = BitVec.ofNat 32 padr ∧ σ "perm" = BitVec.ofNat 32 perm ∧
        ATInv maxpage kl kh d.toPData ∧ (d.AC nn).cusage ≤ (d.AC nn).cquota ∧
        ∃ d1 r, ptInsert_spec maxpage num_proc nn vadr padr perm d = some (d1, r))
      (ptInsertS cb maxpage pb fb)
      (fun _ d σ' d' => ∃ r, ptInsert_spec maxpage num_proc nn vadr padr perm d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hn, hva, hpa, hpe, hI, hu, dF, rF, hs⟩
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb; have := hL.hcb
  have hs0 := hs
  unfold ptInsert_spec at hs
  have hc : d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg num_proc nn vadr padr d.nps := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg num_proc nn vadr padr d.nps
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hinit, hipt, hpg, ⟨hn0, hnp, hlo, hhi⟩, hpa0, hpan⟩ := hc
  have hv : vadr < 2 ^ 32 := by omega
  have hpdx : PDX vadr < 1024 := by unfold PDX; omega
  have hnpsm : d.nps ≤ maxpage := hI.valid_nps.2
  have hmagic : maxpage + 1 < 2 ^ 32 := by omega
  cases hz : ZtoPerm perm with
  | none => rw [hz] at hs; cases hs
  | some p =>
    rw [hz] at hs; simp only at hs
    -- what pt_read_pde leaves alone
    have frR : ∀ (τ : Locals) (lb : RLog), Runs (rprimsA εR c) (ptReadPDES pb) σ l τ lb →
        ∀ z : Ident, z ≠ "i" → z ≠ "r" → τ z = σ z := fun τ lb hr z h1 h2 =>
      hr.frame (by simp [frS, ptReadPDES, withPDX, getPDES, Ne.symm h1, Ne.symm h2])
    cases hp : d.ptpool nn (PDX vadr) with
    | PDEID => rw [hp] at hs; cases hs
    | PDEUndef => rw [hp] at hs; cases hs
    | PDEValid pi pdt =>
      rw [hp] at hs; simp only at hs
      cases hI2 : ptInsertPTE_spec nn vadr padr p d with
      | none => rw [hI2] at hs; cases hs
      | some d2 =>
        rw [hI2] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
        obtain ⟨hpi0, hpil⟩ := insertPTE_pi_pos hI2 hp
        have e1 : ptReadPDE_spec num_proc nn vadr d = some pi := by
          unfold ptReadPDE_spec getPDE_spec; rw [if_pos ⟨hinit, hipt, hnp, hpdx⟩, hp]
        obtain ⟨σ1, l1, b1, d1, hr1, hcs1, hM1, hlk1, -, hd1, v, hsv, hrv⟩ :=
          ptReadPDE_triple εR c i0 (pb := pb) (num_proc := num_proc) (by omega) nn vadr hv σ l b d hlk hcs hM
            ⟨hn, hva, pi, e1⟩
        rw [hd1] at hM1
        rw [e1] at hsv; simp only [Option.some.injEq] at hsv
        have fr1 := frR σ1 l1 hr1
        have hg1 : σ1 "r" ≠ 0 := by
          have hne : (BitVec.ofNat 32 pi : Val) ≠ BitVec.ofNat 32 0 :=
            KernPAlloc.ofNat_ne (a := pi) (b := 0) (by omega) (by decide) (by omega)
          rw [hrv, ← hsv]; exact hne
        let σ2 := σ1.set "res" 0
        have ha2 : Runs (rprimsA εR c) (.assign "res" (.const 0)) σ1 l1 σ2 l1 := Runs.assign _ _
        have hg2 : σ2 "res" ≠ BitVec.ofNat 32 (maxpage + 1) := by
          have : (BitVec.ofNat 32 0 : Val) ≠ BitVec.ofNat 32 (maxpage + 1) :=
            KernPAlloc.ofNat_ne (by decide) hmagic (by omega)
          simpa [σ2] using this
        obtain ⟨σ3, l3, b3, hr3, hcs3, hM3, hlk3, hfr3⟩ :=
          insTail_run εR c i0 hL hmax hmp (σ := σ2) (by simp [σ2, Locals.set, hlk1, hlk]) hcs1 hM1
            (by simp [σ2, Locals.set, fr1, hn]) (by simp [σ2, Locals.set, fr1, hva])
            (by simp [σ2, Locals.set, fr1, hpa]) (by simp [σ2, Locals.set, fr1, hpe])
            hipt hnp hv hz ⟨hpa0, hpan⟩ hnpsm hI2
        have hres3 : σ3 "res" = 0 := by
          rw [hfr3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [σ2]
        have ha3 : Runs (rprimsA εR c) (.assign "r" (.var "res")) σ3 l3 (σ3.set "r" 0) l3 := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σ3) (l := l3) "r" (.var "res")
          have e : (Expr.var "res").eval σ3 = 0 := hres3
          rw [e] at h; exact h
        refine ⟨_, l3, b3, d2, Runs.seq hr1 (Runs.seq (Runs.ite_true (ne_true hg1) ha2)
          (Runs.seq (Runs.ite_true (ne_true hg2) hr3) ha3)), hcs3, hM3, ?_,
          fun k hk => absurd trivial hk, 0, by rw [hs0, hdF, hrF], by simp⟩
        rw [Locals.set_other _ _ (by decide), hlk3]; simp [σ2, Locals.set, hlk1]
    | PDEUnPresent =>
      rw [hp] at hs; simp only at hs
      cases hAl : ptAllocPDE_spec num_proc nn vadr d with
      | none => rw [hAl] at hs; cases hs
      | some pr =>
        obtain ⟨d2, v⟩ := pr
        rw [hAl] at hs; simp only at hs
        obtain ⟨hnps2, hipt2, hvr⟩ := allocPDE_facts hAl
        have e1 : ptReadPDE_spec num_proc nn vadr d = some 0 := by
          unfold ptReadPDE_spec getPDE_spec; rw [if_pos ⟨hinit, hipt, hnp, hpdx⟩, hp]
        obtain ⟨σ1, l1, b1, d1, hr1, hcs1, hM1, hlk1, -, hd1, v1, hsv, hrv⟩ :=
          ptReadPDE_triple εR c i0 (pb := pb) (num_proc := num_proc) (by omega) nn vadr hv σ l b d hlk hcs hM
            ⟨hn, hva, 0, e1⟩
        rw [hd1] at hM1
        rw [e1] at hsv; simp only [Option.some.injEq] at hsv
        have fr1 := frR σ1 l1 hr1
        have hg1 : σ1 "r" = 0 := by rw [hrv, ← hsv]; rfl
        -- pt_alloc_pde
        obtain ⟨σ2, l2, b2, d2', hr2, hcs2, hM2, hlk2, -, r, hsr, hrr⟩ :=
          ptAllocPDE_triple εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh) nn vadr σ1 l1 b1 d
            (by rw [hlk1]; exact hlk) hcs1 hM1
            ⟨by rw [fr1 _ (by decide) (by decide)]; exact hn, by rw [fr1 _ (by decide) (by decide)]; exact hva,
              hI, hu, _, _, hAl⟩
        rw [hAl] at hsr
        simp only [Option.some.injEq, Prod.mk.injEq] at hsr; obtain ⟨hd2, hvr'⟩ := hsr
        rw [← hd2] at hM2; rw [← hvr'] at hrr
        have fr2 : ∀ z : Ident, z = "n" ∨ z = "vaddr" ∨ z = "padr" ∨ z = "perm" → σ2 z = σ z := by
          intro z hz
          have h1 : σ2 z = σ1 z := by
            rcases hz with rfl | rfl | rfl | rfl <;>
              exact hr2.frame (by simp [frS, ptAllocPDES, ctAllocCS, pallocCS, getNpsS, pallocLoop, loopBody,
                isNormS, atGetS, atSetS, atSetCS, ptInsertPDES, withPDX, setPDEUS, rmvLoop, rmvPTES,
                pteStoreS])
          rw [h1]
          rcases hz with rfl | rfl | rfl | rfl <;> exact fr1 _ (by decide) (by decide)
        let σ3 := σ2.set "res" (BitVec.ofNat 32 v)
        have ha3 : Runs (rprimsA εR c) (.assign "res" (.var "r")) σ2 l2 σ3 l2 := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σ2) (l := l2) "res" (.var "r")
          have e : (Expr.var "r").eval σ2 = BitVec.ofNat 32 v := hrr
          rw [e] at h; exact h
        have hlk3 : (σ3 "lk").toNat = i0 := by simp [σ3, Locals.set, hlk2, hlk1, hlk]
        by_cases hv0 : v = 0
        · rw [if_pos hv0] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
          let σ4 := σ3.set "res" (BitVec.ofNat 32 (maxpage + 1))
          have ha4 : Runs (rprimsA εR c) (.assign "res" (.const (BitVec.ofNat 32 (maxpage + 1)))) σ3 l2 σ4 l2 :=
            Runs.assign _ _
          have ha5 : Runs (rprimsA εR c) (.assign "r" (.var "res")) σ4 l2
              (σ4.set "r" (BitVec.ofNat 32 (maxpage + 1))) l2 := by
            have h := Runs.assign (P := rprimsA εR c) (σ := σ4) (l := l2) "r" (.var "res")
            have e : (Expr.var "res").eval σ4 = BitVec.ofNat 32 (maxpage + 1) := by show σ4 "res" = _; simp [σ4]
            rw [e] at h; exact h
          refine ⟨_, l2, b2, d2, Runs.seq hr1 (Runs.seq (Runs.ite_false (ne_false hg1)
            (Runs.seq hr2 (Runs.seq ha3 (Runs.ite_true (eq_true (by simp [σ3, hv0])) ha4))))
            (Runs.seq (Runs.ite_false (ne_false (by simp [σ4])) Runs.skip) ha5)), hcs2, hM2, ?_,
            fun k hk => absurd trivial hk, maxpage + 1, by rw [hs0, hdF, hrF], by simp⟩
          rw [Locals.set_other _ _ (by decide)]; simp [σ4, σ3, Locals.set, hlk2, hlk1]
        · rw [if_neg hv0] at hs
          have hvb : 0 < v ∧ v < d.nps := by rcases hvr with h | h; exact absurd h hv0; exact h
          cases hI2 : ptInsertPTE_spec nn vadr padr p d2 with
          | none => rw [hI2] at hs; cases hs
          | some d3 =>
            rw [hI2] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
            have hne0 : σ3 "res" ≠ 0 := by
              have : (BitVec.ofNat 32 v : Val) ≠ BitVec.ofNat 32 0 :=
                KernPAlloc.ofNat_ne (by omega) (by decide) (by omega)
              simpa [σ3] using this
            have hneM : σ3 "res" ≠ BitVec.ofNat 32 (maxpage + 1) := by
              have : (BitVec.ofNat 32 v : Val) ≠ BitVec.ofNat 32 (maxpage + 1) :=
                KernPAlloc.ofNat_ne (by omega) hmagic (by omega)
              simpa [σ3] using this
            obtain ⟨σ5, l5, b5, hr5, hcs5, hM5, hlk5, hfr5⟩ :=
              insTail_run εR c i0 hL hmax hmp (σ := σ3) hlk3 hcs2 hM2
                (by simp [σ3, Locals.set, fr2, hn]) (by simp [σ3, Locals.set, fr2, hva])
                (by simp [σ3, Locals.set, fr2, hpa]) (by simp [σ3, Locals.set, fr2, hpe])
                (by rw [hipt2]; exact hipt) hnp hv hz ⟨hpa0, by rw [hnps2]; exact hpan⟩
                (by rw [hnps2]; exact hnpsm) hI2
            have hres5 : σ5 "res" = BitVec.ofNat 32 v := by
              rw [hfr5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [σ3]
            have ha6 : Runs (rprimsA εR c) (.assign "r" (.var "res")) σ5 l5 (σ5.set "r" (BitVec.ofNat 32 v)) l5 := by
              have h := Runs.assign (P := rprimsA εR c) (σ := σ5) (l := l5) "r" (.var "res")
              have e : (Expr.var "res").eval σ5 = BitVec.ofNat 32 v := hres5
              rw [e] at h; exact h
            refine ⟨_, l5, b5, d3, Runs.seq hr1 (Runs.seq (Runs.ite_false (ne_false hg1)
              (Runs.seq hr2 (Runs.seq ha3 (Runs.ite_false (eq_false hne0) Runs.skip))))
              (Runs.seq (Runs.ite_true (ne_true hneM) hr5) ha6)), hcs5, hM5, ?_,
              fun k hk => absurd trivial hk, v, by rw [hs0, hdF, hrF], by simp⟩
            rw [Locals.set_other _ _ (by decide), hlk5]; simp [σ3, Locals.set, hlk2, hlk1]

end Insert

/-! ## `pt_rmv` -/

/-- `padr / PAGESIZE` -/
def pgE : Expr := .bin .div (.var "padr") (.const 4096)

/-- ```
padr = pt_read(n, vadr);
if (padr != 0) {
  pt_rmv_aux(n, vadr);
  count = at_get_c(padr / PAGESIZE);
  if (count > 0) at_set_c(padr / PAGESIZE, count - 1);
}
return padr / PAGESIZE;
``` -/
def ptRmvS (pb fb : Nat) : Stmt APrim :=
  .seq (ptReadS pb fb) (.seq (.assign "padr" (.var "r"))
    (.seq (.ite (.bin .ne (.var "padr") (.const 0))
        (.seq (ptRmvAuxS pb fb) (.seq (atGetCS "count" pgE)
          (.ite (.bin .ltu (.const 0) (.var "count"))
            (atSetCS pgE (.bin .sub (.var "count") (.const 1))) .skip)))
        .skip)
      (.assign "r" pgE)))

section Rmv
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **`pt_rmv` refines `ptRmv_spec`.** -/
theorem ptRmv_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) (nn vadr : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => True)
      (fun σ d => σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ∃ d1 r, ptRmv_spec maxpage num_proc nn vadr d = some (d1, r))
      (ptRmvS pb fb)
      (fun _ d σ' d' => ∃ r, ptRmv_spec maxpage num_proc nn vadr d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hn, hva, dF, rF, hs⟩
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb; have := hL.hcb
  have hs0 := hs
  unfold ptRmv_spec at hs
  have hc : d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg' num_proc nn vadr := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg' num_proc nn vadr
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hinit, hipt, hpg, hn0, hnp, hlo, hhi⟩ := hc
  have hv : vadr < 2 ^ 32 := by omega
  have hpdx : PDX vadr < 1024 := by unfold PDX; omega
  have hptx : PTX vadr < 1024 := by unfold PTX; omega
  have hPT : ¬ nn = d.PT := by
    intro h; rw [if_pos h] at hs; cases hs
  rw [if_neg hPT] at hs
  cases hp : d.ptpool nn (PDX vadr) with
  | PDEID => rw [hp] at hs; cases hs
  | PDEUnPresent => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEValid pi pdt =>
    rw [hp] at hs; simp only at hs
    have frR : ∀ (τ : Locals) (lb : RLog), Runs (rprimsA εR c) (ptReadS pb fb) σ l τ lb →
        ∀ z : Ident, z ≠ "i" → z ≠ "vadr" → z ≠ "o" → z ≠ "r" → τ z = σ z := fun τ lb hr z h1 h2 h3 h4 =>
      hr.frame (by simp [frS, ptReadS, withPDXPTX, getPTES, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4])
    cases hq : pdt (PTX vadr) with
    | PTEUndef => rw [hq] at hs; cases hs
    | PTEUnPresent =>
      rw [hq] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
      have e1 : ptRead_spec num_proc nn vadr d = some 0 := by
        unfold ptRead_spec getPTE_spec
        rw [if_pos ⟨hinit, hipt, ⟨hnp, hpdx⟩, hptx⟩, hp]; simp only; rw [hq]
      obtain ⟨σ1, l1, b1, d1, hr1, hcs1, hM1, hlk1, -, hd1, v, hsv, hrv⟩ :=
        ptRead_triple εR c i0 (pb := pb) (fb := fb) (num_proc := num_proc) (by omega) (by omega) nn vadr hv
          σ l b d hlk hcs hM ⟨hn, hva, 0, e1⟩
      rw [hd1] at hM1
      rw [e1] at hsv; simp only [Option.some.injEq] at hsv
      let σ2 := σ1.set "padr" (BitVec.ofNat 32 0)
      have ha2 : Runs (rprimsA εR c) (.assign "padr" (.var "r")) σ1 l1 σ2 l1 := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l1) "padr" (.var "r")
        have e : (Expr.var "r").eval σ1 = BitVec.ofNat 32 0 := by rw [← hsv] at hrv; exact hrv
        rw [e] at h; exact h
      have ha3 : Runs (rprimsA εR c) (.assign "r" pgE) σ2 l1 (σ2.set "r" (BitVec.ofNat 32 0)) l1 := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σ2) (l := l1) "r" pgE
        have e : pgE.eval σ2 = BitVec.ofNat 32 0 := by
          show σ2 "padr" / 4096 = _; simp [σ2]
        rw [e] at h; exact h
      refine ⟨_, l1, b1, d, Runs.seq hr1 (Runs.seq ha2 (Runs.seq (Runs.ite_false (ne_false (by simp [σ2]))
        Runs.skip) ha3)), hcs1, hM1, ?_, fun k hk => absurd trivial hk, 0, by rw [hs0, hdF, hrF], by simp⟩
      rw [Locals.set_other _ _ (by decide)]; simp [σ2, Locals.set, hlk1]
    | PTEValid padr p =>
      rw [hq] at hs; simp only at hs
      have hpr : 0 < padr ∧ padr < maxpage := by
        by_cases h : 0 < padr ∧ padr < maxpage
        · exact h
        · rw [if_neg h] at hs; cases hs
      rw [if_pos hpr] at hs
      cases hA : d.AT padr with
      | ATUndef => rw [hA] at hs; cases hs
      | ATValid b0 t cnt =>
        rw [hA] at hs
        cases b0 <;> cases t <;> simp only at hs <;> try (cases hs)
        have hcl : 0 < cnt ∧ cnt ≤ 2 ^ 32 - 1 := by
          by_cases h : 0 < cnt ∧ cnt ≤ 2 ^ 32 - 1
          · exact h
          · rw [if_neg h] at hs; cases hs
        rw [if_pos hcl] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
        have hpm := perm_le p
        have hW : padr * 4096 + PermtoZ p < 2 ^ 32 := by omega
        -- pt_read
        have e1 : ptRead_spec num_proc nn vadr d = some (padr * 4096 + PermtoZ p) := by
          unfold ptRead_spec getPTE_spec
          rw [if_pos ⟨hinit, hipt, ⟨hnp, hpdx⟩, hptx⟩, hp]; simp only; rw [hq]
        obtain ⟨σ1, l1, b1, d1, hr1, hcs1, hM1, hlk1, -, hd1, v, hsv, hrv⟩ :=
          ptRead_triple εR c i0 (pb := pb) (fb := fb) (num_proc := num_proc) (by omega) (by omega) nn vadr hv
            σ l b d hlk hcs hM ⟨hn, hva, _, e1⟩
        rw [hd1] at hM1
        rw [e1] at hsv; simp only [Option.some.injEq] at hsv
        have fr1 := frR σ1 l1 hr1
        let σ2 := σ1.set "padr" (BitVec.ofNat 32 (padr * 4096 + PermtoZ p))
        have ha2 : Runs (rprimsA εR c) (.assign "padr" (.var "r")) σ1 l1 σ2 l1 := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l1) "padr" (.var "r")
          have e : (Expr.var "r").eval σ1 = BitVec.ofNat 32 (padr * 4096 + PermtoZ p) := by
            rw [← hsv] at hrv; exact hrv
          rw [e] at h; exact h
        have hg : σ2 "padr" ≠ 0 := by
          have hne : (BitVec.ofNat 32 (padr * 4096 + PermtoZ p) : Val) ≠ BitVec.ofNat 32 0 :=
            KernPAlloc.ofNat_ne (a := padr * 4096 + PermtoZ p) (b := 0) hW (by decide) (by omega)
          simpa [σ2] using hne
        -- the page number
        have hpg : ∀ τ : Locals, τ "padr" = BitVec.ofNat 32 (padr * 4096 + PermtoZ p) →
            pgE.eval τ = BitVec.ofNat 32 padr := by
          intro τ hτ
          show τ "padr" / 4096 = _
          rw [hτ]
          refine val_of_toNat ?_ (by omega)
          rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW]
          show (padr * 4096 + PermtoZ p) / 4096 = padr
          omega
        -- pt_rmv_aux
        have e2 : ptRmvAux_spec num_proc nn vadr d = some { d with
            ptpool := setAt d.ptpool nn (setAt (d.ptpool nn) (PDX vadr)
              (.PDEValid pi (setAt pdt (PTX vadr) .PTEUnPresent))) } := by
          unfold ptRmvAux_spec rmvPTE_spec
          rw [if_pos ⟨hinit, hipt, ⟨hnp, hpdx⟩, hptx⟩, if_neg hPT, hp]
        obtain ⟨σ3, l3, b3, d3, hr3, hcs3, hM3, hlk3, -, hq3⟩ :=
          ptRmvAux_triple εR c i0 hL nn vadr hv σ2 l1 b1 d (by simp [σ2, Locals.set, hlk1, hlk]) hcs1 hM1
            ⟨by simp [σ2, Locals.set, fr1, hn], by simp [σ2, Locals.set, fr1, hva], _, e2⟩
        rw [e2] at hq3; simp only [Option.some.injEq] at hq3
        rw [← hq3] at hM3
        have hpa3 : σ3 "padr" = BitVec.ofNat 32 (padr * 4096 + PermtoZ p) := by
          rw [hr3.frame (by simp [frS, ptRmvAuxS, withPDXPTX, rmvPTES, pteStoreS])]; simp [σ2]
        -- count = at_get_c(padr / PAGESIZE)
        have e3 : get_at_c_spec maxpage padr (PTData.toRData { d with
            ptpool := setAt d.ptpool nn (setAt (d.ptpool nn) (PDX vadr)
              (.PDEValid pi (setAt pdt (PTX vadr) .PTEUnPresent))) }).toPData = some cnt := by
          unfold get_at_c_spec
          rw [if_pos hpr.2]
          show (match d.AT padr with
            | .ATValid _ _ n => some n
            | .ATUndef => none) = some cnt
          rw [hA]
        obtain ⟨σ4, l4, b4, d4, hr4, hcs4, hM4, hlk4, -, hd4, v4, hsv4, hσ4⟩ :=
          atGetC_lift εR c i0 hL hmax "count" (by decide) pgE padr σ3 l3 b3 _
            (by rw [hlk3]; simp [σ2, Locals.set, hlk1, hlk]) hcs3 hM3 ⟨hpg σ3 hpa3, _, e3⟩
        rw [e3] at hsv4; simp only [Option.some.injEq] at hsv4
        rw [hd4] at hM4
        have hcnt4 : σ4 "count" = BitVec.ofNat 32 cnt := by rw [hσ4, Locals.set_same, ← hsv4]
        have hpa4 : σ4 "padr" = BitVec.ofNat 32 (padr * 4096 + PermtoZ p) := by
          rw [hσ4, Locals.set_other _ _ (by decide)]; exact hpa3
        have hgc : ¬ (Expr.bin .ltu (.const 0) (.var "count")).eval σ4 = 0 := by
          show ¬ (if (0 : Val).ult (σ4 "count") then (1 : Val) else 0) = 0
          have := ult_ofNat (m := 0) (n := cnt) (by decide) (by omega)
          rw [hcnt4, show (0 : Val) = BitVec.ofNat 32 0 from rfl, this]; simp [hcl.1]
        -- at_set_c(padr / PAGESIZE, count - 1)
        have e4 : set_at_c_spec maxpage padr (cnt - 1) (PTData.toRData { d with
            ptpool := setAt d.ptpool nn (setAt (d.ptpool nn) (PDX vadr)
              (.PDEValid pi (setAt pdt (PTX vadr) .PTEUnPresent))) }).toPData =
            some { d.toPData with AT := setAt d.AT padr (.ATValid true .ATNorm (cnt - 1)) } := by
          unfold set_at_c_spec
          rw [if_pos hpr.2]
          show (match d.AT padr with
            | .ATValid b .ATNorm _ => some { d.toPData with AT := setAt d.AT padr (.ATValid b .ATNorm (cnt - 1)) }
            | _ => none) = _
          rw [hA]
        obtain ⟨σ5, l5, b5, d5, hr5, hcs5, hM5, hlk5, -, r1, hd5, ⟨pd, hpd, hr1e⟩, hσ5⟩ :=
          atSetC_lift εR c i0 hL hmax pgE (.bin .sub (.var "count") (.const 1)) padr (cnt - 1)
            σ4 l4 b4 _ (by rw [hlk4, hlk3]; simp [σ2, Locals.set, hlk1, hlk]) hcs4 hM4
            ⟨hpg σ4 hpa4, by
              show σ4 "count" - 1 = _
              rw [hcnt4]
              have h1 : (1 : Val).toNat = 1 := rfl
              have hc1 := hcl.1
              have hc2 := hcl.2
              refine val_of_toNat ?_ (by omega)
              rw [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
              omega, by have := hcl.2; omega, _, e4⟩
        rw [e4] at hpd; simp only [Option.some.injEq] at hpd
        rw [hd5, hr1e, ← hpd] at hM5
        have hpa5 : σ5 "padr" = BitVec.ofNat 32 (padr * 4096 + PermtoZ p) := by
          rw [hσ5, Locals.set_other _ _ (by decide)]; exact hpa4
        have ha6 : Runs (rprimsA εR c) (.assign "r" pgE) σ5 l5 (σ5.set "r" (BitVec.ofNat 32 padr)) l5 := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σ5) (l := l5) "r" pgE
          rw [hpg σ5 hpa5] at h; exact h
        refine ⟨_, l5, b5, dF, Runs.seq hr1 (Runs.seq ha2 (Runs.seq (Runs.ite_true (ne_true hg)
          (Runs.seq hr3 (Runs.seq hr4 (Runs.ite_true hgc hr5)))) ha6)), hcs5, ?_, ?_,
          fun k hk => absurd trivial hk, padr, by rw [hs0, hrF], by simp⟩
        · rw [← hdF]; exact hM5
        · rw [Locals.set_other _ _ (by decide), hlk5, hlk4, hlk3]; simp [σ2, Locals.set, hlk1]

end Rmv

end MPTKern
