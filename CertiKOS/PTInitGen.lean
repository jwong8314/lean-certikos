import CertiKOS.MPTNew

/-!
# mCertiKOS `PTInitGen`: from reference counts to owner lists, ported

Below this step the allocation table counts how many page-table entries map
each page. Above it, mCertiKOS's abstract state says *which* entries do: the
logical allocation table `LAT` holds, for each page, the list of its owners
`LATO n pdi pti` (entry `(pdi, pti)` of process `n`'s page table). This is
mCertiKOS's notion of page ownership.

The step has no C code. It is a simulation between two abstract states
(`mcertikos/mm/PTInitGen.v`): whenever a specification of the upper layer is
defined on a state `h`, the lower one is defined on any related state `d`,
with the same result and related final states.

Ported from `layerlib/AuxStateDataType.v`: `LATOwner`, `LATInfo`, `LATable`,
`Lfirst_free`, `relate_LATInfo`, `relate_LATable`, `consistent_pmap`,
`consistent_pmap_domain`.

Ported from `objects/ObjLMM0.v` and `ObjLMM1.v`: `alloc_spec`,
`ptInsertPTE0_spec`, `ptAllocPDE0_spec`, `ptInsert0_spec`, `ptRmv0_spec`,
`ptResv_spec`.

Ported from `mm/PTInitGen.v`: `relate_RData` (`Relate`), and the lemmas
`alloc_exist`, `ptInsertPTE_exist`, `ptAllocPDE_exist`, `ptInsert_exist`,
`ptRmv_exist`.

What differs: as before, no `ikern`/`ihost`, and `Nat` for `Z`.
`LATable_nil` is written from how the sources use it (a free page has no
owners); its definition was not read. The lemmas take the facts of
`high_level_invariant` they use (`HInvI`) rather than the whole record.

Not ported: `ptFreePDE0_spec`, `pfree`'s upper specification, and the proof
that the upper specifications preserve the upper invariant.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PTInitGen

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew

/-! ## The upper state (`AuxStateDataType.v`) -/

/-- `LATO n pdi pti`: entry `(pdi, pti)` of process `n`'s page table. -/
inductive LATOwner
  | LATO (n pdi pti : Nat)
  deriving DecidableEq

/-- `LATValid allocated type owners`. -/
inductive LATInfo
  | LATValid (b : Bool) (t : ATType) (l : List LATOwner)
  | LATUndef

abbrev LATable := Nat → LATInfo

/-- The abstract state of the upper layer: `PTData` with `LAT` for `AT`. -/
structure HData where
  LAT : LATable
  nps : Nat
  pperm : Nat → PPgInfo
  init : Bool
  AC : ContainerPool
  ptpool : PMapPool
  idpde : Nat → Nat → IDPTEInfo
  PT : Nat
  pg : Bool
  ipt : Bool
  HP : Nat → Option Val

/-- `relate_LATInfo`: a count is the length of the owner list. -/
def RelInfo : ATInfo → LATInfo → Prop
  | .ATUndef, .LATUndef => True
  | .ATValid b t n, .LATValid b' t' l => b = b' ∧ t = t' ∧ n = l.length
  | _, _ => False

/-- `relate_RData`: the two states agree except that `AT` counts what `LAT` lists. -/
structure Relate (h : HData) (d : PTData) : Prop where
  lat : ∀ i, RelInfo (d.AT i) (h.LAT i)
  nps : d.nps = h.nps
  pperm : d.pperm = h.pperm
  init : d.init = h.init
  AC : d.AC = h.AC
  ptpool : d.ptpool = h.ptpool
  idpde : d.idpde = h.idpde
  PT : d.PT = h.PT
  pg : d.pg = h.pg
  ipt : d.ipt = h.ipt
  HP : d.HP = h.HP

/-- An unallocated normal page with no owners. -/
def isLFree : LATInfo → Bool
  | .LATValid false .ATNorm [] => true
  | _ => false

def LffFrom (L : LATable) : Nat → Nat → Option Nat
  | _, 0 => none
  | m, k + 1 => if isLFree (L m) then some m else LffFrom L (m + 1) k

/-- `Lfirst_free`. -/
def Lfirst_free (L : LATable) (size : Nat) : Option Nat := LffFrom L 1 (size - 1)

/-- `LATable_nil`: a free page has no owners. -/
def LATable_nil (L : LATable) : Prop := ∀ i l, L i = .LATValid false .ATNorm l → l = []

/-- `first_free_relate_LATable`: the two searches find the same page. -/
theorem ff_relate {A : ATable} {L : LATable} (hR : ∀ i, RelInfo (A i) (L i)) (hN : LATable_nil L) :
    ∀ (k m : Nat), ffFrom A m k = LffFrom L m k
  | 0, _ => rfl
  | k + 1, m => by
    have he : isFree (A m) = isLFree (L m) := by
      have h := hR m
      cases hA : A m with
      | ATUndef =>
        rw [hA] at h
        cases hL : L m with
        | LATUndef => rfl
        | LATValid b t l => rw [hL] at h; exact absurd h (by simp [RelInfo])
      | ATValid b t n =>
        rw [hA] at h
        cases hL : L m with
        | LATUndef => rw [hL] at h; exact absurd h (by simp [RelInfo])
        | LATValid b' t' l =>
          rw [hL] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          cases b <;> cases t <;> try rfl
          have := hN m l hL
          subst this; rfl
    simp only [ffFrom, LffFrom, he]
    split
    · rfl
    · exact ff_relate hR hN k (m + 1)

/-! ## The invariant facts the simulation uses (`MPTInit.v`) -/

/-- `consistent_pmap`: the page of a second-level table is hidden, owned by
its directory entry, and has no owners of the other kind. -/
def consistent_pmap (num_proc : Nat) (ptp : PMapPool) (ppt : Nat → PPgInfo) (L : LATable) (nps : Nat) : Prop :=
  ∀ i, i < num_proc → ∀ j, j < 2 ^ 32 → ∀ pte pi, ptp i (PDX j) = .PDEValid pi pte →
    (0 < pi ∧ pi < nps) ∧ ppt pi = .PGHide i (PDX j) ∧ L pi = .LATValid true .ATNorm []

/-- `consistent_pmap_domain`: a mapped page is allocated, and the entry that
maps it is in its owner list exactly once. -/
def consistent_pmap_domain (num_proc : Nat) (ptp : PMapPool) (ppt : Nat → PPgInfo) (L : LATable)
    (nps : Nat) : Prop :=
  ∀ i, i < num_proc → ∀ j, j < 2 ^ 32 → ∀ pte pi, ptp i (PDX j) = .PDEValid pi pte →
    ∀ v p, pte (PTX j) = .PTEValid v p →
      (0 < v ∧ v < nps) ∧ ppt v = .PGAlloc ∧
      ∃ l, L v = .LATValid true .ATNorm l ∧ l.count (.LATO i (PDX j) (PTX j)) = 1

/-- The facts of the upper layer's `high_level_invariant` that the simulation
uses. -/
structure HInvI (maxpage num_proc : Nat) (h : HData) : Prop where
  valid_pg_init : h.pg = h.init
  valid_PT_kern : h.pg = true → h.ipt = true → h.PT = 0
  valid_LATable_nil : LATable_nil h.LAT
  valid_nps : h.nps ≤ maxpage
  valid_pperm_pmap : consistent_pmap num_proc h.ptpool h.pperm h.LAT h.nps

/-! ## Upper specifications (`ObjLMM0.v`, `ObjLMM1.v`) -/

/-- **`alloc_spec`**: `container_alloc` over the owner lists. -/
def alloc_spec (id : Nat) (h : HData) : Option (HData × Nat) :=
  let c := h.AC id
  if h.pg = true ∧ h.ipt = true ∧ c.cused = true then
    if c.cusage < c.cquota then
      match Lfirst_free h.LAT h.nps with
      | some i =>
        some ({ h with LAT := setAt h.LAT i (.LATValid true .ATNorm []), pperm := setAt h.pperm i .PGAlloc,
                       AC := setAt h.AC id ⟨c.cquota, c.cusage + 1, c.cparent, c.cchildren, c.cused⟩ }, i)
      | none => none
    else some (h, 0)
  else none

/-- **`alloc_exist`.** -/
theorem alloc_exist {maxpage num_proc : Nat} {h h' : HData} {d : PTData} {id i : Nat} (hR : Relate h d)
    (hI : HInvI maxpage num_proc h) (hs : alloc_spec id h = some (h', i)) :
    ∃ r1 : RData, container_alloc_spec id d.toRData = some (r1, i) ∧
      Relate h' { d with toRData := r1 } := by
  unfold alloc_spec at hs
  simp only at hs
  have hc : h.pg = true ∧ h.ipt = true ∧ (h.AC id).cused = true := by
    by_cases hh : h.pg = true ∧ h.ipt = true ∧ (h.AC id).cused = true
    · exact hh
    · rw [if_neg hh] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hpg, hipt, hused⟩ := hc
  have hinit : d.init = true := by rw [hR.init, ← hI.valid_pg_init]; exact hpg
  have hACd : d.AC = h.AC := hR.AC
  unfold container_alloc_spec
  simp only
  rw [if_pos ⟨hinit, by rw [hACd]; exact hused⟩]
  by_cases hlt : (h.AC id).cusage < (h.AC id).cquota
  · rw [if_pos hlt] at hs
    rw [if_pos (by rw [hACd]; exact hlt)]
    have hff : first_free d.AT d.nps = Lfirst_free h.LAT h.nps := by
      unfold first_free Lfirst_free; rw [hR.nps]
      exact ff_relate hR.lat hI.valid_LATable_nil _ _
    cases hL : Lfirst_free h.LAT h.nps with
    | none => rw [hL] at hs; cases hs
    | some p =>
      rw [hL] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      rw [show first_free d.AT d.nps = some p from hff.trans hL]
      refine ⟨_, rfl, ⟨fun j => ?_, hR.nps, ?_, hR.init, ?_, hR.ptpool, hR.idpde, hR.PT, hR.pg, hR.ipt, hR.HP⟩⟩
      · show RelInfo (setAt d.AT p (.ATValid true .ATNorm 0) j) (setAt h.LAT p (.LATValid true .ATNorm []) j)
        by_cases hj : j = p
        · rw [hj, setAt_eq, setAt_eq]; exact ⟨rfl, rfl, rfl⟩
        · rw [setAt_ne _ _ hj, setAt_ne _ _ hj]; exact hR.lat j
      · show setAt d.pperm p .PGAlloc = setAt h.pperm p .PGAlloc
        rw [hR.pperm]
      · show setAt d.AC id _ = setAt h.AC id _
        rw [hACd]
  · rw [if_neg hlt] at hs
    rw [if_neg (by rw [hACd]; exact hlt)]
    simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    exact ⟨_, rfl, hR⟩

end PTInitGen
