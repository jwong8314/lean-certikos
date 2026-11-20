import CertiKOS.MShare
import CertiKOS.LayerStep

/-!
# The machine model, first part: `CR3`, the paging bit, and `pt_init`

mCertiKOS's bottom layer (`PreInit`) has two trusted primitives for the
CPU's control registers: `set_cr3` loads `CR3` and `set_pg` sets the paging
bit of `CR0`. Their specifications (`setCR3_spec`, `setPG_spec`) are part of
the machine model. Everything about paging is built on them.

**The model here.** The two registers are two words of the kernel region, at
`cpub` and `cpub + 1`. `set_cr3` and `set_pg` write them. `MatchCPU` ties
them to the abstract state: `CR3` holds the address of directory `PT`
(mCertiKOS's `relate_PT`), and the paging word is nonzero exactly when `pg`
holds. Until now `pg` and `PT` were fields no cell constrained.

Ported from `layerlib/AuxStateDataType.v`: `PDE_kern`, `PMap_common`,
`PMap_kern`, `PDE_usr`, `PMap_usr`, `PMap_valid`. Ported from
`clib/CalRealPT.v`: `real_pt_PMap_valid`, `real_pt_PMap_kern`.

Ported from `objects/ObjVMMGetSet.v`: `setPT'_spec`. From `objects/ObjCPU.v`:
`setPG1_spec`. From `objects/ObjLMM1.v`: `pt_init_spec`, `pmap_init_spec`.
Ported from `mm/MContainerCSource.v`, `mm/MPTKernCSource.v`,
`mm/MPTInitCSource.v`: the C code of `set_pt`, `pt_init`, `pmap_init`.

* `setPT_triple`, `setPG_triple`: `set_pt` and `set_pg` refine their
  specifications.
* `pt_init_factors`: `pt_init_spec` is `pt_init_kern_spec`, then
  `setPT'_spec 0`, then `setPG1_spec`. The two side conditions are that the
  kernel's page table is valid and maps the kernel by the identity
  (`real_pt_PMap_valid`, `real_pt_PMap_kern`); they are what makes turning
  paging on safe.
* `pt_init_triple`: **`pt_init` refines `pt_init_spec`.** After it `pg` is
  true, in the abstract state and in the region.

What this model leaves out: there is one `CR3` and one paging bit, as in
single-core mCertiKOS, not one per CPU. The registers are written with the
kernel lock held. No access goes through the page table: kernel code runs on
the identity map, and user-mode accesses are not modelled yet. `ikern` and
`ihost` are still dropped.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MCPU

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew
open MALInit (rd_run wr_run tn MMTable MatchMMap matchMM_of_eq MM_valid MM_correct real_AT real_nps)
open MPTInit

/-! ## Valid page tables (`AuxStateDataType.v`) -/

/-- `PDE_kern`: the directory entry of page `i` is the identity. -/
def PDE_kern (pmap : PMap) (i : Nat) : Prop := pmap (PDX (i * 4096)) = .PDEID

/-- `PMap_common`: outside the user range every table is the identity. -/
def PMap_common (maxpage kl kh : Nat) (pmap : PMap) : Prop :=
  ∀ i, i < kl ∨ (kh ≤ i ∧ i < maxpage) → PDE_kern pmap i

/-- `PMap_kern`: the kernel's table is the identity on the user range too. -/
def PMap_kern (kl kh : Nat) (pmap : PMap) : Prop := ∀ i, kl ≤ i → i < kh → PDE_kern pmap i

def PDE_usr (pmap : PMap) (i : Nat) : Prop :=
  pmap (PDX (i * 4096)) = .PDEUnPresent ∨ pmap (PDX (i * 4096)) = .PDEID ∨
    ∃ pte pi, pmap (PDX (i * 4096)) = .PDEValid pi pte ∧ pte (PTX (i * 4096)) ≠ .PTEUndef

def PMap_usr (kl kh : Nat) (pmap : PMap) : Prop := ∀ i, kl ≤ i → i < kh → PDE_usr pmap i

def PMap_valid (maxpage kl kh : Nat) (pmap : PMap) : Prop :=
  PMap_common maxpage kl kh pmap ∧ PMap_usr kl kh pmap

/-! ## The initial page tables, entry by entry (`CalRealPT.v`) -/

theorem at_get (j n : Nat) (ptp : PMapPool) (n' i' : Nat) :
    Calculate_PDE_at_i j n ptp n' i' =
      if n' = n ∧ i' = j then (if 256 ≤ j ∧ j < 960 then PDE.PDEUnPresent else PDE.PDEID) else ptp n' i' := by
  unfold Calculate_PDE_at_i
  by_cases e : n' = n ∧ i' = j
  · rw [if_pos e]
    obtain ⟨e1, e2⟩ := e
    subst e1; subst e2
    by_cases h1 : 256 ≤ i'
    · rw [if_pos h1]
      by_cases h2 : i' < 960
      · rw [if_pos h2, pool_get_eq, if_pos ⟨h1, h2⟩]
      · rw [if_neg h2, pool_get_eq, if_neg (fun h => h2 h.2)]
    · rw [if_neg h1, pool_get_eq, if_neg (fun h => h1 h.1)]
  · rw [if_neg e]
    by_cases h1 : 256 ≤ j
    · rw [if_pos h1]
      by_cases h2 : j < 960
      · rw [if_pos h2, pool_get_ne _ _ e]
      · rw [if_neg h2, pool_get_ne _ _ e]
    · rw [if_neg h1, pool_get_ne _ _ e]

theorem rowQ_get (n : Nat) (ptp : PMapPool) : ∀ (j n' i' : Nat), rowQ n j ptp n' i' =
    if n' = n ∧ i' < j then (if 256 ≤ i' ∧ i' < 960 then PDE.PDEUnPresent else PDE.PDEID) else ptp n' i'
  | 0, n', i' => by
    have e0 : ¬ (n' = n ∧ i' < 0) := fun h => Nat.not_lt_zero _ h.2
    rw [if_neg e0]; rfl
  | j + 1, n', i' => by
    show Calculate_PDE_at_i j n (rowQ n j ptp) n' i' = _
    rw [at_get, rowQ_get n ptp j n' i']
    by_cases e : n' = n ∧ i' = j
    · have e3 : n' = n ∧ i' < j + 1 := ⟨e.1, by have := e.2; omega⟩
      rw [if_pos e, if_pos e3, e.2]
    · rw [if_neg e]
      by_cases e2 : n' = n ∧ i' < j
      · have e3 : n' = n ∧ i' < j + 1 := ⟨e2.1, by have := e2.2; omega⟩
        rw [if_pos e2, if_pos e3]
      · have e3 : ¬ (n' = n ∧ i' < j + 1) := fun h => by
          by_cases h' : i' < j
          · exact e2 ⟨h.1, h'⟩
          · exact e ⟨h.1, by have := h.2; omega⟩
        rw [if_neg e2, if_neg e3]

theorem allQ_get (ptp : PMapPool) : ∀ (m n' i' : Nat), i' < 1024 → allQ m ptp n' i' =
    if n' < m then (if 256 ≤ i' ∧ i' < 960 then PDE.PDEUnPresent else PDE.PDEID) else ptp n' i'
  | 0, n', i', _ => by
    have e0 : ¬ n' < 0 := Nat.not_lt_zero _
    rw [if_neg e0]; rfl
  | m + 1, n', i', hi => by
    show rowQ m 1024 (allQ m ptp) n' i' = _
    rw [rowQ_get, allQ_get ptp m n' i' hi]
    by_cases e : n' = m
    · have e1 : n' = m ∧ i' < 1024 := ⟨e, hi⟩
      have e2 : n' < m + 1 := by omega
      rw [if_pos e1, if_pos e2]
    · have e1 : ¬ (n' = m ∧ i' < 1024) := fun h => e h.1
      rw [if_neg e1]
      by_cases e2 : n' < m
      · have e3 : n' < m + 1 := by omega
        rw [if_pos e2, if_pos e3]
      · have e3 : ¬ n' < m + 1 := by omega
        rw [if_neg e2, if_neg e3]

theorem kern_at_get (i : Nat) (ptp : PMapPool) (n' i' : Nat) :
    Calculate_pt_kern_at_i i ptp n' i' = if n' = 0 ∧ i' = i then PDE.PDEID else ptp n' i' := by
  unfold Calculate_pt_kern_at_i
  by_cases e : n' = 0 ∧ i' = i
  · rw [if_pos e]
    obtain ⟨e1, e2⟩ := e
    subst e1; subst e2
    rw [pool_get_eq]
  · rw [if_neg e, pool_get_ne _ _ e]

theorem kernQ_get (ptp : PMapPool) : ∀ (j n' i' : Nat), kernQ j ptp n' i' =
    if n' = 0 ∧ 256 ≤ i' ∧ i' < 256 + j then PDE.PDEID else ptp n' i'
  | 0, n', i' => by
    have e0 : ¬ (n' = 0 ∧ 256 ≤ i' ∧ i' < 256 + 0) := fun h => by have := h.2.1; have := h.2.2; omega
    rw [if_neg e0]; rfl
  | j + 1, n', i' => by
    show Calculate_pt_kern_at_i (j + 256) (kernQ j ptp) n' i' = _
    rw [kern_at_get, kernQ_get ptp j n' i']
    by_cases e : n' = 0 ∧ i' = j + 256
    · have e3 : n' = 0 ∧ 256 ≤ i' ∧ i' < 256 + (j + 1) :=
        ⟨e.1, by have := e.2; omega, by have := e.2; omega⟩
      rw [if_pos e, if_pos e3]
    · rw [if_neg e]
      by_cases e2 : n' = 0 ∧ 256 ≤ i' ∧ i' < 256 + j
      · have e3 : n' = 0 ∧ 256 ≤ i' ∧ i' < 256 + (j + 1) := ⟨e2.1, e2.2.1, by have := e2.2.2; omega⟩
        rw [if_pos e2, if_pos e3]
      · have e3 : ¬ (n' = 0 ∧ 256 ≤ i' ∧ i' < 256 + (j + 1)) := fun h => by
          by_cases h' : i' < 256 + j
          · exact e2 ⟨h.1, h.2.1, h'⟩
          · exact e ⟨h.1, by have := h.2.2; omega⟩
        rw [if_neg e2, if_neg e3]

/-- **`real_pt`, entry by entry**: the kernel's directory is the identity
everywhere; the others are the identity outside `[256, 960)` and empty
inside. -/
theorem real_pt_get {num_proc : Nat} (h : 0 < num_proc) (ptp : PMapPool) {n i : Nat} (hn : n < num_proc)
    (hi : i < 1024) :
    real_pt num_proc ptp n i = if (256 ≤ i ∧ i < 960) ∧ n ≠ 0 then PDE.PDEUnPresent else PDE.PDEID := by
  unfold real_pt
  rw [kernQ_calc, allQ_real h, kernQ_get, allQ_get _ _ _ _ hi, if_pos hn]
  by_cases e : n = 0 ∧ 256 ≤ i ∧ i < 256 + (703 + 1)
  · have e1 : ¬ ((256 ≤ i ∧ i < 960) ∧ n ≠ 0) := fun h' => h'.2 e.1
    rw [if_pos e, if_neg e1]
  · rw [if_neg e]
    by_cases e2 : 256 ≤ i ∧ i < 960
    · have e3 : (256 ≤ i ∧ i < 960) ∧ n ≠ 0 := ⟨e2, fun h0 => e ⟨h0, e2.1, by have := e2.2; omega⟩⟩
      rw [if_pos e2, if_pos e3]
    · have e3 : ¬ ((256 ≤ i ∧ i < 960) ∧ n ≠ 0) := fun h' => e2 h'.1
      rw [if_neg e2, if_neg e3]

/-- `real_pt_PMap_kern`: the kernel's table maps every page by the identity. -/
theorem real_pt_PMap_kern {num_proc : Nat} (h : 0 < num_proc) (ptp : PMapPool) {kl kh : Nat}
    (hkh : kh ≤ 2 ^ 20) : PMap_kern kl kh (real_pt num_proc ptp 0) := by
  intro i _ hi2
  unfold PDE_kern
  have hx : PDX (i * 4096) = i / 1024 := by unfold PDX; omega
  have e1 : ¬ ((256 ≤ i / 1024 ∧ i / 1024 < 960) ∧ (0 : Nat) ≠ 0) := fun h' => h'.2 rfl
  rw [hx, real_pt_get h ptp h (by omega), if_neg e1]

/-- `real_pt_PMap_valid`, with mCertiKOS's `kern_low` and `kern_high`. -/
theorem real_pt_PMap_valid {num_proc : Nat} (h : 0 < num_proc) (ptp : PMapPool) {maxpage kl kh n : Nat}
    (hkl : kl = 262144) (hkh : kh = 983040) (hmax : maxpage ≤ 2 ^ 20) (hn : n < num_proc) :
    PMap_valid maxpage kl kh (real_pt num_proc ptp n) := by
  subst hkl; subst hkh
  constructor
  · intro i hi
    unfold PDE_kern
    have hx : PDX (i * 4096) = i / 1024 := by unfold PDX; omega
    have e1 : ¬ ((256 ≤ i / 1024 ∧ i / 1024 < 960) ∧ n ≠ 0) := fun h' => by
      have := h'.1.1; have := h'.1.2; omega
    rw [hx, real_pt_get h ptp hn (by omega), if_neg e1]
  · intro i hi1 hi2
    unfold PDE_usr
    have hx : PDX (i * 4096) = i / 1024 := by unfold PDX; omega
    rw [hx, real_pt_get h ptp hn (by omega)]
    by_cases e : (256 ≤ i / 1024 ∧ i / 1024 < 960) ∧ n ≠ 0
    · rw [if_pos e]; exact Or.inl rfl
    · rw [if_neg e]; exact Or.inr (Or.inl rfl)

/-! ## The control registers in the region -/

/-- `CR3` is the word at `cpub`: the address of the current directory
(`relate_PT`). The paging bit is the word at `cpub + 1`. -/
def MatchCPU (num_proc pb cpub : Nat) (d : PTData) (b : Region) : Prop :=
  (d.PT < num_proc → b cpub = BitVec.ofNat 32 (pb + d.PT * 1024)) ∧ (d.pg = true ↔ b (cpub + 1) ≠ 0)

/-- The layout with the two register words between the containers and the
page-table pool. -/
structure MLayout (maxpage num_id cb num_proc pb ib fb cpub : Nat) : Prop where
  lay : Layout maxpage num_id cb num_proc pb ib fb
  hc0 : cb + 5 * num_id ≤ cpub
  hc1 : cpub + 2 ≤ pb

/-- The memory-management region with the control registers. -/
def MatchM (maxpage num_id cb num_proc pb ib fb ida cpub : Nat) (d : PTData) (b : Region) : Prop :=
  MatchAll maxpage num_id cb num_proc pb ib fb ida d b ∧ MatchCPU num_proc pb cpub d b

section Frame
variable {maxpage num_id cb num_proc pb ib fb ida cpub : Nat}

/-- The layers up to the page tables depend only on the cells below the end
of the containers and from the page-table pool on. -/
theorem matchAll_gap (hL : Layout maxpage num_id cb num_proc pb ib fb) {d : PTData} {b b' : Region}
    (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida d b)
    (hfr : ∀ k, k < cb + 5 * num_id ∨ pb ≤ k → b' k = b k) :
    MatchAll maxpage num_id cb num_proc pb ib fb ida d b' := by
  have := hL.hcb; have := hL.hpb
  have hb : ∀ k, k < cb + 5 * num_id → b' k = b k := fun k hk => hfr k (Or.inl hk)
  refine ⟨⟨⟨fun j hj => ?_, ?_⟩, fun j hj => ?_⟩,
    matchpt_transfer hL hM.pt (fun k hk => hfr k (Or.inr hk)) rfl rfl rfl (fun _ _ _ _ => rfl)⟩
  · rw [hb _ (by omega), hb _ (by omega), hb _ (by omega)]; exact hM.mm.mAT.mat j hj
  · rw [hb _ (by omega)]; exact hM.mm.mAT.mnps
  · rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]
    exact hM.mm.mAC j hj

/-- No cell of the layers below holds `PT`. -/
theorem matchAll_PT {d : PTData} {b : Region} (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida d b)
    (n : Nat) : MatchAll maxpage num_id cb num_proc pb ib fb ida { d with PT := n } b :=
  ⟨hM.mm, ⟨hM.pt.pool, hM.pt.idp, hM.pt.pte, hM.pt.hp, hM.pt.hid⟩⟩

/-- No cell of the layers below holds `pg`. -/
theorem matchAll_pg {d : PTData} {b : Region} (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida d b)
    (p : Bool) : MatchAll maxpage num_id cb num_proc pb ib fb ida { d with pg := p } b :=
  ⟨hM.mm, ⟨hM.pt.pool, hM.pt.idp, hM.pt.pte, hM.pt.hp, hM.pt.hid⟩⟩

theorem cpub_lt (hL : MLayout maxpage num_id cb num_proc pb ib fb cpub) : cpub + 1 < 2 ^ 32 := by
  have := hL.hc1; have := hL.lay.hib; have := hL.lay.hfb; have := hL.lay.hend; omega

end Frame

/-! ## The trusted primitives, and `set_pt` -/

/-- `set_cr3(v)`: load `CR3`. -/
def setCR3S (cpub : Nat) (ve : Expr) : Stmt APrim := .call "_" .push [lkE, .const (BitVec.ofNat 32 cpub), ve]

/-- `set_pg()`: set the paging bit. -/
def setPGS (cpub : Nat) : Stmt APrim := .call "_" .push [lkE, .const (BitVec.ofNat 32 (cpub + 1)), .const 1]

/-- `set_pt(index)`: `set_cr3(PTPool_LOC[index]);` -/
def setPTS (pb cpub : Nat) (ie : Expr) : Stmt APrim :=
  setCR3S cpub (.bin .add (.const (BitVec.ofNat 32 pb)) (.bin .mul ie (.const 1024)))

/-! ## Specifications -/

open Classical in
/-- `setPT'_spec` (`ObjVMMGetSet.v`): switch to a valid page table. With the
kernel's page table in use, the new one must map the kernel too. -/
noncomputable def setPT'_spec (maxpage kl kh num_proc n : Nat) (d : PTData) : Option PTData :=
  if n < num_proc then
    if PMap_valid maxpage kl kh (d.ptpool n) then
      if d.ipt = true then
        if PMap_kern kl kh (d.ptpool n) then some { d with PT := n } else none
      else some { d with PT := n }
    else none
  else none

open Classical in
/-- `setPG1_spec` (`ObjCPU.v`): turn paging on, with a valid table loaded
that maps the kernel by the identity. -/
noncomputable def setPG1_spec (maxpage kl kh num_proc : Nat) (d : PTData) : Option PTData :=
  if d.pg = false ∧ d.init = true ∧ d.ipt = true then
    if d.PT < num_proc then
      if PMap_valid maxpage kl kh (d.ptpool d.PT) then
        if PMap_kern kl kh (d.ptpool d.PT) then some { d with pg := true } else none
      else none
    else none
  else none

/-- **`pt_init_spec`** (`ObjLMM1.v`), with the allocation table in place of
the owner lists. -/
def pt_init_spec (num_proc kl kh : Nat) (mm : MMTable) (size : Nat) (d : PTData) : Option PTData :=
  if d.init = false ∧ d.pg = false ∧ d.ipt = true then
    some { d with
      pg := true
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc d.ptpool
      idpde := real_idpde d.idpde }
  else none

/-- `pmap_init_spec`: the same function, one layer up. -/
def pmap_init_spec (num_proc kl kh : Nat) (mm : MMTable) (size : Nat) (d : PTData) : Option PTData :=
  pt_init_spec num_proc kl kh mm size d

/-- **`pt_init_spec` is its three calls**: `pt_init_kern`, `set_pt(0)`,
`set_pg()`, each by its own specification. -/
theorem pt_init_factors {num_proc kl kh maxpage : Nat} {mm : MMTable} {size : Nat} (hnp : 0 < num_proc)
    (hkl : kl = 262144) (hkh : kh = 983040) (hmax : maxpage ≤ 2 ^ 20) {d d' : PTData}
    (hs : pt_init_spec num_proc kl kh mm size d = some d') :
    ∃ d1 d2, pt_init_kern_spec num_proc kl kh mm size d = some d1 ∧
      setPT'_spec maxpage kl kh num_proc 0 d1 = some d2 ∧ setPG1_spec maxpage kl kh num_proc d2 = some d' := by
  unfold pt_init_spec at hs
  by_cases hc : d.init = false ∧ d.pg = false ∧ d.ipt = true
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    have hv : PMap_valid maxpage kl kh (real_pt num_proc d.ptpool 0) :=
      real_pt_PMap_valid hnp _ hkl hkh hmax hnp
    have hk : PMap_kern kl kh (real_pt num_proc d.ptpool 0) :=
      real_pt_PMap_kern hnp _ (by rw [hkh]; decide)
    let d1 : PTData := { d with
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      ptpool := real_pt num_proc d.ptpool
      idpde := real_idpde d.idpde }
    have h1 : pt_init_kern_spec num_proc kl kh mm size d = some d1 := by
      unfold pt_init_kern_spec; rw [if_pos hc]
    have h2 : setPT'_spec maxpage kl kh num_proc 0 d1 = some { d1 with PT := 0 } := by
      have hv' : PMap_valid maxpage kl kh (d1.ptpool 0) := hv
      have hk' : PMap_kern kl kh (d1.ptpool 0) := hk
      have hi' : d1.ipt = true := hc.2.2
      unfold setPT'_spec
      rw [if_pos hnp, if_pos hv', if_pos hi', if_pos hk']
    let d2 : PTData := { d1 with PT := 0 }
    have h3 : setPG1_spec maxpage kl kh num_proc d2 = some { d2 with pg := true } := by
      have hf : d2.pg = false ∧ d2.init = true ∧ d2.ipt = true := ⟨hc.2.1, rfl, hc.2.2⟩
      have hp : d2.PT < num_proc := hnp
      have hv' : PMap_valid maxpage kl kh (d2.ptpool d2.PT) := hv
      have hk' : PMap_kern kl kh (d2.ptpool d2.PT) := hk
      unfold setPG1_spec
      rw [if_pos hf, if_pos hp, if_pos hv', if_pos hk']
    exact ⟨d1, d2, h1, h2, h3⟩
  · rw [if_neg hc] at hs; cases hs

/-! ## The code -/

/-- `pt_init(mbi_adr)`: `pt_init_kern(mbi_adr); set_pt(0); set_pg();` -/
def ptInitCS (mmb maxpage kl kh cb num_proc pb ib ida cpub : Nat) : Stmt APrim :=
  .seq (ptInitKernCS mmb maxpage kl kh cb num_proc pb ib ida) (.seq (setPTS pb cpub (.const 0)) (setPGS cpub))

/-- `pmap_init(mbi_adr)`: `pt_init(mbi_adr);` -/
def pmapInitCS (mmb maxpage kl kh cb num_proc pb ib ida cpub : Nat) : Stmt APrim :=
  ptInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub

/-- The two register words. -/
def CF (cpub : Nat) (k : Nat) : Prop := k = cpub ∨ k = cpub + 1

section Steps
variable {maxpage num_id cb num_proc pb ib fb ida cpub : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MM" => MatchM maxpage num_id cb num_proc pb ib fb ida cpub

/-- `set_pt(n)`: `CR3` now points at directory `n`. -/
theorem setPT_step (hL : MLayout maxpage num_id cb num_proc pb ib fb cpub) (hF : ∀ k, CF cpub k → F k)
    {ie : Expr} {σ : Locals} {d : PTData} {n : Nat} (he : ie.eval σ = BitVec.ofNat 32 n) :
    Step εR c i0 MM F (setPTS pb cpub ie) σ d (σ.set "_" 0) { d with PT := n } := by
  have := hL.hc0; have := hL.hc1; have := cpub_lt hL
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  have hv : (Expr.bin .add (.const (BitVec.ofNat 32 pb)) (.bin .mul ie (.const 1024))).eval σ =
      BitVec.ofNat 32 (pb + n * 1024) := by
    show BitVec.ofNat 32 pb + ie.eval σ * (1024 : Val) = _
    rw [he, show (1024 : Val) = BitVec.ofNat 32 1024 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (.const (BitVec.ofNat 32 cpub)) _ (n := cpub)
    (tn (by omega)) hv
  refine ⟨l', _, hr, hcs', ⟨matchAll_PT (matchAll_gap hL.lay hM.1 (fun k hk => sc_ne _ _ (by omega))) n,
    fun _ => sc_eq _ _ _, ?_⟩, fun k hk => sc_ne _ _ (fun e => hk (hF k (Or.inl e)))⟩
  rw [sc_ne _ _ (by omega)]
  exact hM.2.2

/-- `set_pg()`: paging is on. -/
theorem setPG_step (hL : MLayout maxpage num_id cb num_proc pb ib fb cpub) (hF : ∀ k, CF cpub k → F k)
    (σ : Locals) (d : PTData) :
    Step εR c i0 MM F (setPGS cpub) σ d (σ.set "_" 0) { d with pg := true } := by
  have := hL.hc0; have := hL.hc1; have := cpub_lt hL
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (.const (BitVec.ofNat 32 (cpub + 1))) (.const 1)
    (n := cpub + 1) (v := 1) (tn (by omega)) rfl
  refine ⟨l', _, hr, hcs', ⟨matchAll_pg (matchAll_gap hL.lay hM.1 (fun k hk => sc_ne _ _ (by omega))) true,
    fun h => ?_, ?_⟩, fun k hk => sc_ne _ _ (fun e => hk (hF k (Or.inr e)))⟩
  · rw [sc_ne _ _ (by omega)]
    exact hM.2.1 h
  · rw [sc_eq]
    exact ⟨fun _ => by decide, fun _ => rfl⟩

/-- **`set_pt` refines `setPT'_spec`.** -/
theorem setPT_triple (hL : MLayout maxpage num_id cb num_proc pb ib fb cpub) {kl kh : Nat} (ie : Expr)
    (n : Nat) :
    Triple εR c i0 MM (CF cpub)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ d1, setPT'_spec maxpage kl kh num_proc n d = some d1)
      (setPTS pb cpub ie)
      (fun σ d σ' d' => setPT'_spec maxpage kl kh num_proc n d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, d1, hs⟩ => ?_)
  have hd1 : d1 = { d with PT := n } := by
    unfold setPT'_spec at hs
    repeat' (split at hs)
    all_goals first | (cases hs; rfl) | cases hs
  subst hd1
  exact ⟨_, _, setPT_step εR c i0 hL (fun _ h => h) he, hs, rfl⟩

/-- **`set_pg` refines `setPG1_spec`.** -/
theorem setPG_triple (hL : MLayout maxpage num_id cb num_proc pb ib fb cpub) {kl kh : Nat} :
    Triple εR c i0 MM (CF cpub)
      (fun _ d => ∃ d1, setPG1_spec maxpage kl kh num_proc d = some d1)
      (setPGS cpub)
      (fun σ d σ' d' => setPG1_spec maxpage kl kh num_proc d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨d1, hs⟩ => ?_)
  have hd1 : d1 = { d with pg := true } := by
    unfold setPG1_spec at hs
    repeat' (split at hs)
    all_goals first | (cases hs; rfl) | cases hs
  subst hd1
  exact ⟨_, _, setPG_step εR c i0 hL (fun _ h => h) σ d, hs, rfl⟩

/-- **`pt_init` refines `pt_init_spec`**: the kernel's page table is built,
`CR3` points at it, and paging is on. -/
theorem pt_init_triple (hL : MLayout maxpage num_id cb num_proc pb ib fb cpub)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {mmb size kl kh : Nat} {mm : MMTable}
    (hcm : cb + 5 * num_id ≤ mmb) (hmb : mmb + 1 + 3 * size ≤ cpub) (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0 (fun (d : PTData) b => MM d b ∧ MatchMMap mmb mm size b)
      (fun k => (k < cb + 5 * num_id ∨ pb ≤ k) ∨ CF cpub k)
      (fun _ d => d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ (∀ j, (d.AC j).cused = false) ∧ NV d.ptpool)
      (ptInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub)
      (fun _ d _ d' => pt_init_spec num_proc kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨⟨hA, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have := hL.hc0; have := hL.hc1
  obtain ⟨σ1, l1, b1, d1, hr1, hcs1, ⟨hA1, hMM1⟩, hlk1, hf1, hq1⟩ :=
    pt_init_kern_triple εR c i0 hL.lay hida hnp hcm (by omega) hnum hmp hkl hkl' hkh hsz hv hc σ l b d hlk hcs
      ⟨hA, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hd1 : d1 = { d with
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      ptpool := real_pt num_proc d.ptpool
      idpde := real_idpde d.idpde } := by
    have h : pt_init_kern_spec num_proc kl kh mm size d = some d1 := hq1
    unfold pt_init_kern_spec at h
    rw [if_pos ⟨hin, hpg, hipt⟩] at h
    exact (Option.some.inj h).symm
  have hg : ∀ k, cb + 5 * num_id ≤ k → k < pb → b1 k = b k := fun k h1 h2 =>
    hf1 k (by rintro (h | h) <;> omega)
  have hC1 : MatchCPU num_proc pb cpub d1 b1 := by
    rw [hd1]
    refine ⟨fun h => ?_, ?_⟩
    · rw [hg cpub (by omega) (by omega)]; exact hC.1 h
    · rw [hg (cpub + 1) (by omega) (by omega)]; exact hC.2
  have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
  obtain ⟨l2, b2, hr2, hcs2, hM2, hf2⟩ := (setPT_step εR c i0 hL (F := CF cpub) (fun _ h => h)
    (ie := .const 0) (σ := σ1) (d := d1) (n := 0) rfl).2 l1 b1 hlk1' hcs1 ⟨hA1, hC1⟩
  obtain ⟨l3, b3, hr3, hcs3, hM3, hf3⟩ := (setPG_step εR c i0 hL (F := CF cpub) (fun _ h => h)
    (σ1.set "_" 0) { d1 with PT := 0 }).2 l2 b2 (by simpa [Locals.set] using hlk1') hcs2 hM2
  have hcf : ∀ k, ¬ CF cpub k → b3 k = b1 k := fun k hk => (hf3 k hk).trans (hf2 k hk)
  refine ⟨_, l3, b3, _, Runs.seq hr1 (Runs.seq hr2 hr3), hcs3,
    ⟨hM3, matchMM_of_eq hMM1 (fun k hk hk2 => hcf k (by rintro (h | h) <;> omega))⟩, ?_, fun k hk => ?_, ?_⟩
  · simp [Locals.set, hlk1]
  · rw [hcf k (fun h => hk (Or.inr h)), hf1 k (fun h => hk (Or.inl h))]
  · show pt_init_spec num_proc kl kh mm size d = some _
    unfold pt_init_spec
    rw [if_pos ⟨hin, hpg, hipt⟩, hd1]

end Steps

end MCPU
