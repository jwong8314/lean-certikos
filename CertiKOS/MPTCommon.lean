import CertiKOS.MPTOp

/-!
# mCertiKOS `MPTCommon`: allocating and freeing second-level tables, ported

The primitives mCertiKOS builds from the page-table operations and the
allocator (`mcertikos/mm/MPTOpCSource.v`).

Ported from `objects/ObjVMMFun.v`: `ptFreePDE_spec`, and `pt_Arg'` from
`layerlib/AuxStateDataType.v`.

Ported from `mm/MPTOpCSource.v`: `pt_free_pde`.

`pt_free_pde` calls three primitives of the layers below: `pt_read_pde`,
`pt_rmv_pde` and `pfree`. Its proof uses their triples only. `pfree` was
verified on the allocation table and containers alone. `Layer.Triple.lift`
carries it to the state with page tables (`pfree_lift`).

Not yet ported: `pt_alloc_pde`, `pt_init_comm`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MPTCommon

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp

theorem setAt_setAt {α : Type} (f : Nat → α) (i : Nat) (a v : α) : setAt (setAt f i a) i v = setAt f i v := by
  funext k; unfold setAt; split <;> rfl

/-- `pt_Arg'`: a process index and a user virtual address. -/
def pt_Arg' (num_proc n vadr : Nat) : Prop :=
  0 < n ∧ n < num_proc ∧ 1073741824 ≤ vadr ∧ vadr < 4026531840

instance (num_proc n vadr : Nat) : Decidable (pt_Arg' num_proc n vadr) := by
  unfold pt_Arg'; exact inferInstance

/-- **`ptFreePDE_spec`**: remove the second-level table of `vadr` and free its page. -/
def ptFreePDE_spec (maxpage num_proc : Nat) (n vadr : Nat) (d : PTData) : Option PTData :=
  if d.init = true ∧ d.ipt = true ∧ pt_Arg' num_proc n vadr then
    if n = d.PT then none
    else
      match d.ptpool n (PDX vadr) with
      | .PDEValid pi _ =>
        if pi < maxpage then
          match d.pperm pi with
          | .PGHide _ _ =>
            match d.AT pi with
            | .ATValid true .ATNorm 0 =>
              let pt' := setAt (d.ptpool n) (PDX vadr) .PDEUnPresent
              some { d with AT := setAt d.AT pi (.ATValid false .ATNorm 0),
                            pperm := setAt d.pperm pi .PGUndef, ptpool := setAt d.ptpool n pt' }
            | _ => none
          | _ => none
        else none
      | _ => none
  else none

section Lift
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- The page tables do not notice a change below them that keeps the hidden
pages' permissions. -/
theorem matchpt_transfer (hL : Layout maxpage num_id cb num_proc pb ib fb) {d d2 : PTData} {b b' : Region}
    (hM : MatchPT num_proc pb ib fb ida d b) (hb : ∀ k, pb ≤ k → b' k = b k)
    (h1 : d2.ptpool = d.ptpool) (h2 : d2.idpde = d.idpde) (h3 : d2.HP = d.HP)
    (hp : ∀ pi n i, d.pperm pi = .PGHide n i → d2.pperm pi = d.pperm pi) :
    MatchPT num_proc pb ib fb ida d2 b' := by
  have := hL.hib; have := hL.hfb
  refine ⟨fun n i hn hi => ?_, fun i j hi hj => ?_, fun n i pi pdx hn hi hq vadr hv => ?_,
    fun a v hav => ?_, fun n i pi pdx hn hi hq a ha => ?_⟩
  · rw [h1, hb _ (by omega)]
    have old := hM.pool n i hn hi
    cases hq : d.ptpool n i with
    | PDEValid pi pdx => rw [hq] at old; exact ⟨old.1, (hp _ _ _ old.2).trans old.2⟩
    | PDEID => rw [hq] at old; exact old
    | PDEUnPresent => rw [hq] at old; exact old
    | PDEUndef => trivial
  · rw [h2, hb _ (by omega)]; exact hM.idp i j hi hj
  · rw [h1] at hq; rw [hb _ (by omega)]; exact hM.pte n i pi pdx hn hi hq vadr hv
  · rw [h3] at hav; rw [hb _ (by omega)]; exact hM.hp a v hav
  · rw [h1] at hq; rw [h3]; exact hM.hid n i pi pdx hn hi hq a ha

/-- `pfree` changes the permission only of the page it frees, which was `PGAlloc`. -/
theorem pfree_pperm {d pd : PData} {j : Nat} (h : pfree'_spec maxpage j d = some pd) (pi : Nat)
    (hne : d.pperm pi ≠ .PGAlloc) : pd.pperm pi = d.pperm pi := by
  unfold pfree'_spec at h
  by_cases hin : d.init = true
  · rw [if_pos hin] at h
    by_cases hi : j < maxpage
    · rw [if_pos hi] at h
      cases hA : d.AT j with
      | ATUndef => rw [hA] at h; simp at h
      | ATValid b0 t n =>
        rw [hA] at h
        cases hP : d.pperm j <;> rw [hP] at h <;> cases b0 <;> cases t <;> cases n <;> simp at h
        subst h
        exact setAt_ne _ _ (fun e => hne (by rw [e]; exact hP))
    · rw [if_neg hi] at h; cases h
  · rw [if_neg hin] at h; cases h

/-- **`pfree` in the state with page tables.** -/
theorem pfree_lift (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (j : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => k ≤ 3 * maxpage)
      (fun σ d => σ "j" = BitVec.ofNat 32 j ∧ ∃ pd, pfree'_spec maxpage j d.toPData = some pd)
      pfreeCS
      (fun σ d σ' d' => ∃ r1 : RData, d' = { d with toRData := r1 } ∧
        ((∃ pd, pfree'_spec maxpage j d.toPData = some pd ∧ r1 = ⟨pd, d.AC⟩) ∧
          ∀ z, z ≠ "_" → σ' z = σ z)) := by
  have := hL.hcb; have := hL.hpb
  refine ((pfree_triple εR c i0 (num_id := num_id) hmax hL.hcb j).lift (π := PTData.toRData)
    (put := fun (d' : PTData) (r1 : RData) => ({ d' with toRData := r1 } : PTData))
    (M2 := MatchPT num_proc pb ib fb ida) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.mm, h.pt⟩, fun h => ⟨h.1, h.2⟩⟩)
  intro d' b σ σ' d1 b' h2 hM hP hQ hf
  obtain ⟨⟨pd, hs, he⟩, -⟩ := hQ
  subst he
  refine matchpt_transfer hL h2 (fun k hk => hf k (by omega)) rfl rfl rfl (fun pi n i hh => ?_)
  exact pfree_pperm hs pi (by rw [hh]; intro e; cases e)

/-- `container_alloc` gives a permission only to the page it allocates, which
had none. So hidden pages keep theirs. -/
theorem alloc_pperm {kl kh : Nat} {d d1 : RData} {id r : Nat} (hI : ATInv maxpage kl kh d.toPData)
    (h : container_alloc_spec id d = some (d1, r)) (pi n i : Nat) (hh : d.pperm pi = .PGHide n i) :
    d1.pperm pi = d.pperm pi := by
  unfold container_alloc_spec at h
  simp only at h
  by_cases hiu : d.init = true ∧ (d.AC id).cused = true
  · rw [if_pos hiu] at h
    by_cases hlt : (d.AC id).cusage < (d.AC id).cquota
    · rw [if_pos hlt] at h
      cases hff : first_free d.AT d.nps with
      | none => rw [hff] at h; cases h
      | some p =>
        rw [hff] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        obtain ⟨hp0, hpn, ⟨cnt, hfree⟩, -⟩ := first_free_some hff
        refine setAt_ne _ _ (fun e => ?_)
        have hc := (hI.valid_pperm p hpn).1 (by rw [← e, hh]; intro x; cases x)
        obtain ⟨m, hm⟩ := hc
        rw [hfree] at hm; cases hm
    · rw [if_neg hlt] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  · rw [if_neg hiu] at h; cases h

/-- **`container_alloc` in the state with page tables.** -/
theorem container_alloc_lift (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : Layout maxpage num_id cb num_proc pb ib fb) (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : cb + 5 * num_id < 2 ^ 32) {kl kh : Nat} (id : Nat) (hid : id < num_id) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => k < cb + 5 * num_id)
      (fun σ d => σ "id" = BitVec.ofNat 32 id ∧ ATInv maxpage kl kh d.toPData ∧
        (d.AC id).cusage ≤ (d.AC id).cquota ∧ ∃ d1 r, container_alloc_spec id d.toRData = some (d1, r))
      (ctAllocCS cb maxpage)
      (fun _ d σ' d' => ∃ r1 : RData, d' = { d with toRData := r1 } ∧
        ∃ r, container_alloc_spec id d.toRData = some (r1, r) ∧ σ' "r" = BitVec.ofNat 32 r) := by
  have := hL.hcb; have := hL.hpb
  refine ((container_alloc_triple εR c i0 (kl := kl) (kh := kh) hmax hL.hcb hnum id hid).lift
    (π := PTData.toRData)
    (put := fun (d' : PTData) (r1 : RData) => ({ d' with toRData := r1 } : PTData))
    (M2 := MatchPT num_proc pb ib fb ida) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.mm, h.pt⟩, fun h => ⟨h.1, h.2⟩⟩)
  intro d' b σ σ' d1 b' h2 hM hP hQ hf
  obtain ⟨r, hs, -⟩ := hQ
  exact matchpt_transfer hL h2 (fun k hk => hf k (by omega)) rfl rfl rfl
    (fun pi n i hh => alloc_pperm hP.2.1 hs pi n i hh)

end Lift

/-! ## `pt_free_pde` -/

/-- ```
pi = pt_read_pde(n, vadr);
pt_rmv_pde(n, vadr);
pfree(pi);
``` -/
def ptFreePDES (pb : Nat) : Stmt APrim :=
  .seq (ptReadPDES pb) (.seq (.assign "j" (.var "r")) (.seq (ptRmvPDES pb) pfreeCS))

section Free
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **`pt_free_pde` refines `ptFreePDE_spec`.** -/
theorem ptFreePDE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (n vadr : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => True)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ∃ d1, ptFreePDE_spec maxpage num_proc n vadr d = some d1)
      (ptFreePDES pb)
      (fun _ d _ d' => ptFreePDE_spec maxpage num_proc n vadr d = some d') := by
  intro σ l b d hlk hcs hM ⟨hn, hva, dF, hs⟩
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb; have := hL.hcb
  have hs0 := hs
  unfold ptFreePDE_spec at hs
  have hc : d.init = true ∧ d.ipt = true ∧ pt_Arg' num_proc n vadr := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ pt_Arg' num_proc n vadr
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hinit, hipt, hn0, hnp, hlo, hhi⟩ := hc
  have hv : vadr < 2 ^ 32 := by omega
  have hpdx : PDX vadr < 1024 := by unfold PDX; omega
  have hPT : ¬ n = d.PT := by
    intro h; rw [if_pos h] at hs; cases hs
  rw [if_neg hPT] at hs
  cases hp : d.ptpool n (PDX vadr) with
  | PDEID => rw [hp] at hs; cases hs
  | PDEUnPresent => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEValid pi pdt =>
    rw [hp] at hs; simp only at hs
    have hpim : pi < maxpage := by
      by_cases h : pi < maxpage
      · exact h
      · rw [if_neg h] at hs; cases hs
    rw [if_pos hpim] at hs
    cases hpp : d.pperm pi with
    | PGUndef => rw [hpp] at hs; cases hs
    | PGAlloc => rw [hpp] at hs; cases hs
    | PGHide a1 a2 =>
      rw [hpp] at hs; simp only at hs
      cases hA : d.AT pi with
      | ATUndef => rw [hA] at hs; cases hs
      | ATValid b0 t cnt =>
        rw [hA] at hs
        cases b0 <;> cases t <;> cases cnt <;> simp at hs
        -- the three specifications below
        have e1 : ptReadPDE_spec num_proc n vadr d = some pi := by
          unfold ptReadPDE_spec getPDE_spec; rw [if_pos ⟨hinit, hipt, hnp, hpdx⟩, hp]
        have e2 : ptRmvPDE_spec num_proc n vadr d = some { d with
            pperm := setAt d.pperm pi .PGAlloc,
            ptpool := setAt d.ptpool n (setAt (d.ptpool n) (PDX vadr) .PDEUnPresent) } := by
          unfold ptRmvPDE_spec rmvPDE_spec
          rw [if_pos ⟨hinit, hipt, hnp, hpdx⟩]
          simp only
          rw [if_neg (fun h => hPT h.1), hp]
          simp only
          rw [hpp]
        -- pt_read_pde
        obtain ⟨σ1, l1, b1, d1, hr1, hcs1, hM1, hlk1, hf1, hd1, v, hsv, hrv⟩ :=
          ptReadPDE_triple εR c i0 (pb := pb) (num_proc := num_proc) (by omega) n vadr hv σ l b d hlk hcs hM
            ⟨hn, hva, pi, e1⟩
        rw [hd1] at hM1
        rw [e1] at hsv; simp only [Option.some.injEq] at hsv; subst hsv
        have fr1 : ∀ z : Ident, z ≠ "i" → z ≠ "r" → σ1 z = σ z := fun z h1 h2 =>
          hr1.frame (by simp [frS, ptReadPDES, withPDX, getPDES, Ne.symm h1, Ne.symm h2])
        -- j = pi
        let σ2 := σ1.set "j" (BitVec.ofNat 32 pi)
        have ha : Runs (rprimsA εR c) (.assign "j" (.var "r")) σ1 l1 σ2 l1 := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l1) "j" (.var "r")
          have e : (Expr.var "r").eval σ1 = BitVec.ofNat 32 pi := hrv
          rw [e] at h; exact h
        -- pt_rmv_pde
        obtain ⟨σ3, l3, b3, d3, hr3, hcs3, hM3, hlk3, hf3, hq3⟩ :=
          ptRmvPDE_triple εR c i0 hL n vadr hv σ2 l1 b1 d
            (by simp [σ2, Locals.set, hlk1, hlk]) hcs1 hM1
            ⟨by simp [σ2, Locals.set, fr1, hn], by simp [σ2, Locals.set, fr1, hva], _, e2⟩
        rw [e2] at hq3; simp only [Option.some.injEq] at hq3; subst hq3
        have fr3 : σ3 "j" = BitVec.ofNat 32 pi := by
          have : σ3 "j" = σ2 "j" := hr3.frame (by simp [frS, ptRmvPDES, withPDX, rmvPDES])
          rw [this]; simp [σ2]
        -- pfree
        have e3 : pfree'_spec maxpage pi (PTData.toRData { d with
            pperm := setAt d.pperm pi .PGAlloc,
            ptpool := setAt d.ptpool n (setAt (d.ptpool n) (PDX vadr) .PDEUnPresent) }).toPData =
            some { d.toPData with AT := setAt d.AT pi (.ATValid false .ATNorm 0),
                                  pperm := setAt (setAt d.pperm pi .PGAlloc) pi .PGUndef } := by
          unfold pfree'_spec
          simp only
          rw [if_pos hinit, if_pos hpim, hA, setAt_eq]
          rfl
        obtain ⟨σ4, l4, b4, d4, hr4, hcs4, hM4, hlk4, hf4, r1, rfl, ⟨pd, hpd, rfl⟩, -⟩ :=
          pfree_lift εR c i0 hL hmax pi σ3 l3 b3 _ (by rw [hlk3]; simp [σ2, Locals.set, hlk1, hlk]) hcs3 hM3
            ⟨fr3, _, e3⟩
        rw [e3] at hpd; simp only [Option.some.injEq] at hpd; subst hpd
        refine ⟨σ4, l4, b4, _, Runs.seq hr1 (Runs.seq ha (Runs.seq hr3 hr4)), hcs4, hM4, ?_,
          fun k hk => absurd trivial hk, ?_⟩
        · rw [hlk4, hlk3]; simp [σ2, Locals.set, hlk1]
        · show ptFreePDE_spec maxpage num_proc n vadr d = some _
          rw [hs0, ← hs]; simp only [setAt_setAt]

end Free

end MPTCommon
