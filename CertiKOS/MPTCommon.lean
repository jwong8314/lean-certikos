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

/-! ## `pt_alloc_pde` -/

/-- A second-level table whose first `k` entries are cleared. -/
def initPTE (k : Nat) : PTE := fun v => if v < k then .PTEUnPresent else .PTEUndef

/-- `real_init_PTE`: all 1024 entries not present. -/
def real_init_PTE : PTE := initPTE 1024

theorem initPTE_zero : initPTE 0 = fun _ => .PTEUndef := by funext v; simp [initPTE]

theorem initPTE_succ (k : Nat) : setAt (initPTE k) k .PTEUnPresent = initPTE (k + 1) := by
  funext v
  unfold setAt initPTE
  by_cases h : v = k
  · subst h; simp
  · by_cases h2 : v < k
    · simp [h, h2, show v < k + 1 by omega]
    · simp [h, h2, show ¬ v < k + 1 by omega]

theorem pool2 (P : PMapPool) (n i : Nat) (a b : PDE) :
    setAt (setAt P n (setAt (P n) i a)) n (setAt ((setAt P n (setAt (P n) i a)) n) i b) =
      setAt P n (setAt (P n) i b) := by
  funext n' i'
  unfold setAt
  by_cases h1 : n' = n <;> by_cases h2 : i' = i <;> simp [h1, h2]

/-- **`ptAllocPDE_spec`**: allocate a page from container `nn`, install it as
the second-level table of `vadr`, with every entry not present. Returns the
page, or 0 if the container is at its quota. -/
def ptAllocPDE_spec (num_proc : Nat) (nn vadr : Nat) (d : PTData) : Option (PTData × Nat) :=
  let c := d.AC nn
  if d.init = true ∧ d.ipt = true ∧ c.cused = true ∧ pt_Arg' num_proc nn vadr then
    if nn = d.PT then none
    else
      match d.ptpool nn (PDX vadr) with
      | .PDEUnPresent =>
        if c.cusage < c.cquota then
          match first_free d.AT d.nps with
          | some pi =>
            let pt' := setAt (d.ptpool nn) (PDX vadr) (.PDEValid pi real_init_PTE)
            some ({ d with HP := free_page pi d.HP, AT := setAt d.AT pi (.ATValid true .ATNorm 0),
                           pperm := setAt d.pperm pi (.PGHide nn (PDX vadr)),
                           ptpool := setAt d.ptpool nn pt',
                           AC := setAt d.AC nn ⟨c.cquota, c.cusage + 1, c.cparent, c.cchildren, c.cused⟩ }, pi)
          | none => none
        else some (d, 0)
      | _ => none
  else none

/-- The state while the new table is being cleared: `k` entries done. -/
def Dk (DE : PTData) (nn pdi p k : Nat) : PTData :=
  { DE with ptpool := setAt DE.ptpool nn (setAt (DE.ptpool nn) pdi (.PDEValid p (initPTE k))) }

theorem rmv_step (num_proc : Nat) {DE : PTData} {nn pdi p k : Nat} (hinit : DE.init = true)
    (hipt : DE.ipt = true) (hnp : nn < num_proc) (hpdx : pdi < 1024) (hk : k < 1024) (hPT : ¬ nn = DE.PT) :
    rmvPTE_spec num_proc nn pdi k (Dk DE nn pdi p k) = some (Dk DE nn pdi p (k + 1)) := by
  unfold rmvPTE_spec Dk
  simp only
  rw [if_pos ⟨hinit, hipt, ⟨hnp, hpdx⟩, hk⟩, if_neg hPT, pool_get_eq]
  simp only [pool2, initPTE_succ]

/-- `while (vadr < 1024) { rmv_PTE(n, i, vadr); vadr++; }` -/
def rmvLoop (pb fb : Nat) : Stmt APrim :=
  .while (.bin .ltu (.var "vadr") (.const 1024))
    (.seq (rmvPTES pb fb) (.assign "vadr" (.bin .add (.var "vadr") (.const 1))))

section Alloc
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- The clearing loop, verified against `rmv_PTE`'s specification. -/
theorem rmvLoop_run (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    {DE : PTData} {nn pdi p : Nat} (hinit : DE.init = true) (hipt : DE.ipt = true) (hnp : nn < num_proc)
    (hpdx : pdi < 1024) (hPT : ¬ nn = DE.PT) :
    ∀ (m k : Nat), k + m = 1024 → ∀ (σ : Locals) (l : RLog) (b : Region), (σ "lk").toNat = i0 →
      CS1 c i0 l b → MatchAll maxpage num_id cb num_proc pb ib fb ida (Dk DE nn pdi p k) b →
      σ "n" = BitVec.ofNat 32 nn → σ "i" = BitVec.ofNat 32 pdi → σ "vadr" = BitVec.ofNat 32 k →
      ∃ σ' l' b', Runs (rprimsA εR c) (rmvLoop pb fb) σ l σ' l' ∧ CS1 c i0 l' b' ∧
        MatchAll maxpage num_id cb num_proc pb ib fb ida (Dk DE nn pdi p 1024) b' ∧ σ' "lk" = σ "lk" ∧
        (∀ z, z ≠ "o" → z ≠ "_" → z ≠ "vadr" → σ' z = σ z) ∧ ∀ k, k < pb → b' k = b k
  | 0, k, hk, σ, l, b, hlk, hcs, hM, hn, hi, hva => by
    have hk' : k = 1024 := by omega
    subst hk'
    have hg : (σ "vadr").ult 1024 = false := by rw [hva]; decide
    refine ⟨σ, l, b, Runs.while_false ?_, hcs, hM, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    show (if (σ "vadr").ult 1024 then (1 : Val) else 0) = 0
    rw [hg]; rfl
  | m + 1, k, hk, σ, l, b, hlk, hcs, hM, hn, hi, hva => by
    have hk1 : k < 1024 := by omega
    have hg : (σ "vadr").ult 1024 = true := by
      rw [hva]
      have := ult_ofNat (m := k) (n := 1024) (by omega) (by decide)
      rw [show (1024 : Val) = BitVec.ofNat 32 1024 from rfl, this]; simp [hk1]
    obtain ⟨σ1, l1, b1, d1, hr1, hcs1, hM1, hlk1, hf1, hq⟩ :=
      rmvPTE_triple εR c i0 hL nn pdi k σ l b (Dk DE nn pdi p k) hlk hcs hM
        ⟨hn, hi, hva, _, rmv_step num_proc hinit hipt hnp hpdx hk1 hPT⟩
    rw [rmv_step num_proc hinit hipt hnp hpdx hk1 hPT] at hq
    simp only [Option.some.injEq] at hq
    rw [← hq] at hM1
    have fr1 : ∀ z : Ident, z ≠ "o" → z ≠ "_" → σ1 z = σ z := fun z h1 h2 =>
      hr1.frame (by simp [frS, rmvPTES, pteStoreS, Ne.symm h1, Ne.symm h2])
    let σ2 := σ1.set "vadr" (BitVec.ofNat 32 (k + 1))
    have ha : Runs (rprimsA εR c) (.assign "vadr" (.bin .add (.var "vadr") (.const 1))) σ1 l1 σ2 l1 := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l1) "vadr" (.bin .add (.var "vadr") (.const 1))
      have e : (Expr.bin .add (.var "vadr") (.const 1)).eval σ1 = BitVec.ofNat 32 (k + 1) := by
        show σ1 "vadr" + 1 = _
        rw [fr1 _ (by decide) (by decide), hva]; simp [BitVec.ofNat_add]
      rw [e] at h; exact h
    obtain ⟨σ', l', b', hr, hcs', hM', hlk', hfr, hfb'⟩ := rmvLoop_run εR c i0 hL hinit hipt hnp hpdx hPT m (k + 1)
      (by omega) σ2 l1 b1 (by simp [σ2, Locals.set, hlk1, hlk]) hcs1 hM1
      (by simp [σ2, Locals.set, fr1, hn]) (by simp [σ2, Locals.set, fr1, hi]) (by simp [σ2])
    refine ⟨σ', l', b', Runs.while_true ?_ (Runs.seq hr1 ha) hr, hcs', hM', ?_, fun z h1 h2 h3 => ?_,
      fun k hk => by rw [hfb' k hk, hf1 k (by omega)]⟩
    · show ¬ (if (σ "vadr").ult 1024 then (1 : Val) else 0) = 0
      rw [hg]; decide
    · rw [hlk']; simp [σ2, Locals.set, hlk1]
    · rw [hfr z h1 h2 h3]; simp [σ2, Locals.set, h3, fr1 z h1 h2]


/-- ```
pi = container_alloc(n);
if (pi != 0) {
  pt_insert_pde(n, vadr, pi);
  pde_index = vadr / (4096 * 1024);
  i = 0;
  while (i < 1024) { rmv_PTE(n, pde_index, i); i++; }
}
return pi;
``` -/
def ptAllocPDES (cb maxpage pb fb : Nat) : Stmt APrim :=
  .seq (.assign "id" (.var "n")) (.seq (ctAllocCS cb maxpage) (.seq (.assign "pi" (.var "r"))
    (.seq (.ite (.bin .ne (.var "pi") (.const 0))
        (.seq (ptInsertPDES pb) (.seq (.assign "i" pdxE) (.seq (.assign "vadr" (.const 0)) (rmvLoop pb fb))))
        .skip)
      (.assign "r" (.var "pi")))))

/-- **`pt_alloc_pde` refines `ptAllocPDE_spec`.** The proof goes through the
specifications of `container_alloc`, `pt_insert_pde` and `rmv_PTE`. -/
theorem ptAllocPDE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (nn vadr : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => k < cb + 5 * num_id ∨ pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ATInv maxpage kl kh d.toPData ∧ (d.AC nn).cusage ≤ (d.AC nn).cquota ∧
        ∃ d1 r, ptAllocPDE_spec num_proc nn vadr d = some (d1, r))
      (ptAllocPDES cb maxpage pb fb)
      (fun _ d σ' d' => ∃ r, ptAllocPDE_spec num_proc nn vadr d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hn, hva, hI, hu, dF, rF, hs⟩
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb; have := hL.hcb
  have hs0 := hs
  unfold ptAllocPDE_spec at hs
  simp only at hs
  have hc : d.init = true ∧ d.ipt = true ∧ (d.AC nn).cused = true ∧ pt_Arg' num_proc nn vadr := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ (d.AC nn).cused = true ∧ pt_Arg' num_proc nn vadr
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hinit, hipt, hused, hn0, hnp, hlo, hhi⟩ := hc
  have hv : vadr < 2 ^ 32 := by omega
  have hpdx : PDX vadr < 1024 := by unfold PDX; omega
  have hPT : ¬ nn = d.PT := by
    intro h; rw [if_pos h] at hs; cases hs
  rw [if_neg hPT] at hs
  have hnps : d.nps ≤ 2 ^ 20 := Nat.le_trans hI.valid_nps.2 hmp
  -- id = n; pi = container_alloc(id)
  let σa := σ.set "id" (BitVec.ofNat 32 nn)
  have ha0 : Runs (rprimsA εR c) (.assign "id" (.var "n")) σ l σa l := by
    have h := Runs.assign (P := rprimsA εR c) (σ := σ) (l := l) "id" (.var "n")
    have e : (Expr.var "n").eval σ = BitVec.ofNat 32 nn := hn
    rw [e] at h; exact h
  have hlka : (σa "lk").toNat = i0 := by simpa [σa, Locals.set] using hlk
  have frA : ∀ (τ : Locals) (lb : RLog), Runs (rprimsA εR c) (ctAllocCS cb maxpage) σa l τ lb →
      τ "n" = BitVec.ofNat 32 nn ∧ τ "vaddr" = BitVec.ofNat 32 vadr := fun τ lb hr =>
    ⟨by rw [hr.frame (by simp [frS, ctAllocCS, pallocCS, getNpsS, pallocLoop, loopBody, isNormS, atGetS,
            atSetS, atSetCS])]; simp [σa, Locals.set, hn],
     by rw [hr.frame (by simp [frS, ctAllocCS, pallocCS, getNpsS, pallocLoop, loopBody, isNormS, atGetS,
            atSetS, atSetCS])]; simp [σa, Locals.set, hva]⟩
  cases hp : d.ptpool nn (PDX vadr) with
  | PDEID => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEValid pi0 pdt0 => rw [hp] at hs; cases hs
  | PDEUnPresent =>
    rw [hp] at hs; simp only at hs
    by_cases hlt : (d.AC nn).cusage < (d.AC nn).cquota
    · rw [if_pos hlt] at hs
      cases hff : first_free d.AT d.nps with
      | none => rw [hff] at hs; cases hs
      | some p =>
        rw [hff] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, rfl⟩ := hs
        obtain ⟨hp0, hpn, -, -⟩ := first_free_some hff
        have eA : container_alloc_spec nn d.toRData = some ({ d.toRData with
            AT := setAt d.AT p (.ATValid true .ATNorm 0), pperm := setAt d.pperm p .PGAlloc,
            AC := setAt d.AC nn ⟨(d.AC nn).cquota, (d.AC nn).cusage + 1, (d.AC nn).cparent,
              (d.AC nn).cchildren, (d.AC nn).cused⟩ }, p) := by
          unfold container_alloc_spec
          simp only
          rw [if_pos ⟨hinit, hused⟩, if_pos hlt, hff]
        obtain ⟨σb, lb, bb, db, hrb, hcsb, hMb, hlkb, hfb, r1, hdb, r, hsr, hrr⟩ :=
          container_alloc_lift εR c i0 hL hmax hnum (kl := kl) (kh := kh) nn (by omega) σa l b d hlka hcs hM
            ⟨by simp [σa], hI, hu, _, _, eA⟩
        rw [eA] at hsr
        simp only [Option.some.injEq, Prod.mk.injEq] at hsr; obtain ⟨hr1, hrp⟩ := hsr
        rw [← hr1] at hdb; rw [← hrp] at hrr
        obtain ⟨hnb, hvab⟩ := frA σb lb hrb
        have hdbi : db.init = true := by rw [hdb]; exact hinit
        have hdbipt : db.ipt = true := by rw [hdb]; exact hipt
        have hdbPT : ¬ nn = db.PT := by rw [hdb]; exact hPT
        have hdbnps : db.nps = d.nps := by rw [hdb]
        have hdbpp : db.pperm p = .PGAlloc := by rw [hdb]; exact setAt_eq _ _ _
        -- pi = r
        let σc := σb.set "pi" (BitVec.ofNat 32 p)
        have hac : Runs (rprimsA εR c) (.assign "pi" (.var "r")) σb lb σc lb := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σb) (l := lb) "pi" (.var "r")
          have e : (Expr.var "r").eval σb = BitVec.ofNat 32 p := hrr
          rw [e] at h; exact h
        have hlkc : (σc "lk").toNat = i0 := by simp [σc, Locals.set, hlkb, hlka]
        have hpne : σc "pi" ≠ 0 := by
          have : (BitVec.ofNat 32 p : Val) ≠ BitVec.ofNat 32 0 := KernPAlloc.ofNat_ne (by omega) (by decide) (by omega)
          simpa [σc] using this
        -- pt_insert_pde
        obtain ⟨DE, hDE⟩ : ∃ DE : PTData, DE = { db with
            HP := free_page p db.HP, pperm := setAt db.pperm p (.PGHide nn (PDX vadr)),
            ptpool := setAt db.ptpool nn (setAt (db.ptpool nn) (PDX vadr) (.PDEValid p (fun _ => .PTEUndef))) } :=
          ⟨_, rfl⟩
        have eE : ptInsertPDE_spec num_proc nn vadr p db = some DE := by
          rw [hDE]
          unfold ptInsertPDE_spec setPDEU_spec
          rw [if_pos ⟨hdbi, hdbipt, hnp, hpdx⟩, if_neg hdbPT, if_pos ⟨hp0, by rw [hdbnps]; exact hpn⟩, hdbpp]
        obtain ⟨σd, ld, bd, dd, hrd, hcsd, hMd, hlkd, hfd, hqd⟩ :=
          ptInsertPDE_triple εR c i0 hL nn vadr p hv σc lb bb db hlkc hcsb hMb
            ⟨by simp [σc, Locals.set, hnb], by simp [σc, Locals.set, hvab], by simp [σc],
              by rw [hdbnps]; exact hnps, _, eE⟩
        rw [eE] at hqd; simp only [Option.some.injEq] at hqd
        rw [← hqd] at hMd
        have frD : ∀ z : Ident, z ≠ "i" → z ≠ "_" → σd z = σc z := fun z h1 h2 =>
          hrd.frame (by simp [frS, ptInsertPDES, withPDX, setPDEUS, Ne.symm h1, Ne.symm h2])
        -- pde_index, i = 0
        let σe := σd.set "i" (BitVec.ofNat 32 (PDX vadr))
        have hae : Runs (rprimsA εR c) (.assign "i" pdxE) σd ld σe ld := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σd) (l := ld) "i" pdxE
          rw [pdx_eval (σ := σd) (v := vadr) (by rw [frD _ (by decide) (by decide)]; simp [σc, Locals.set, hvab])
            hv] at h
          exact h
        let σf := σe.set "vadr" 0
        have haf : Runs (rprimsA εR c) (.assign "vadr" (.const 0)) σe ld σf ld := Runs.assign _ _
        have hDEi : DE.init = true := by rw [hDE]; exact hdbi
        have hDEipt : DE.ipt = true := by rw [hDE]; exact hdbipt
        have hDEPT : ¬ nn = DE.PT := by rw [hDE]; exact hdbPT
        have e0 : Dk DE nn (PDX vadr) p 0 = DE := by
          rw [hDE]; unfold Dk; simp only [pool2, initPTE_zero]
        rw [← e0] at hMd
        obtain ⟨σg, lg, bg, hrg, hcsg, hMg, hlkg, hfrg, hfg⟩ :=
          rmvLoop_run εR c i0 hL hDEi hDEipt hnp hpdx hDEPT 1024 0 rfl σf ld bd
            (by simp [σf, σe, Locals.set, hlkd, hlkc]) hcsd hMd
            (by simp [σf, σe, Locals.set, frD, σc, hnb]) (by simp [σf, σe, Locals.set]) (by simp [σf])
        -- return pi
        have hpig : σg "pi" = BitVec.ofNat 32 p := by
          rw [hfrg _ (by decide) (by decide) (by decide)]
          simp [σf, σe, Locals.set, frD, σc]
        have hah : Runs (rprimsA εR c) (.assign "r" (.var "pi")) σg lg (σg.set "r" (BitVec.ofNat 32 p)) lg := by
          have h := Runs.assign (P := rprimsA εR c) (σ := σg) (l := lg) "r" (.var "pi")
          have e : (Expr.var "pi").eval σg = BitVec.ofNat 32 p := hpig
          rw [e] at h; exact h
        have efin : Dk DE nn (PDX vadr) p 1024 = dF := by
          rw [← hdF, hDE, hdb]; unfold Dk real_init_PTE; simp only [pool2, setAt_setAt, setAt_eq]
        rw [efin] at hMg
        refine ⟨_, lg, bg, dF, Runs.seq ha0 (Runs.seq hrb (Runs.seq hac (Runs.seq (Runs.ite_true (ne_true hpne)
          (Runs.seq hrd (Runs.seq hae (Runs.seq haf hrg)))) hah))), hcsg, hMg, ?_,
          fun k hk => by
            have hk1 : ¬ k < cb + 5 * num_id := fun h => hk (Or.inl h)
            have hk2 : ¬ pb ≤ k := fun h => hk (Or.inr h)
            rw [hfg k (by omega), hfd k hk2, hfb k hk1], p, hs0, by simp⟩
        rw [Locals.set_other _ _ (by decide), hlkg]
        simp [σf, σe, Locals.set, hlkd, σc, hlkb, σa]
    · rw [if_neg hlt] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      have eA : container_alloc_spec nn d.toRData = some (d.toRData, 0) := by
        unfold container_alloc_spec
        simp only
        rw [if_pos ⟨hinit, hused⟩, if_neg hlt]
      obtain ⟨σb, lb, bb, db, hrb, hcsb, hMb, hlkb, hfb, r1, hdb, r, hsr, hrr⟩ :=
        container_alloc_lift εR c i0 hL hmax hnum (kl := kl) (kh := kh) nn (by omega) σa l b d hlka hcs hM
          ⟨by simp [σa], hI, hu, _, _, eA⟩
      rw [eA] at hsr
      simp only [Option.some.injEq, Prod.mk.injEq] at hsr; obtain ⟨hr1, hrp⟩ := hsr
      rw [← hr1] at hdb; rw [← hrp] at hrr
      have hdbd : db = d := hdb
      rw [hdbd] at hMb
      let σc := σb.set "pi" (BitVec.ofNat 32 0)
      have hac : Runs (rprimsA εR c) (.assign "pi" (.var "r")) σb lb σc lb := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σb) (l := lb) "pi" (.var "r")
        have e : (Expr.var "r").eval σb = BitVec.ofNat 32 0 := hrr
        rw [e] at h; exact h
      have hah : Runs (rprimsA εR c) (.assign "r" (.var "pi")) σc lb (σc.set "r" (BitVec.ofNat 32 0)) lb := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σc) (l := lb) "r" (.var "pi")
        have e : (Expr.var "pi").eval σc = BitVec.ofNat 32 0 := by show σc "pi" = _; simp [σc]
        rw [e] at h; exact h
      refine ⟨_, lb, bb, d, Runs.seq ha0 (Runs.seq hrb (Runs.seq hac (Runs.seq (Runs.ite_false
        (ne_false (by simp [σc])) Runs.skip) hah))), hcsb, hMb, ?_, fun k hk => hfb k (fun h => hk (Or.inl h)), 0, hs0,
        by simp⟩
      rw [Locals.set_other _ _ (by decide)]
      simp [σc, Locals.set, hlkb, σa]

end Alloc

end MPTCommon
