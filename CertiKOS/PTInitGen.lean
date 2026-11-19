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
  valid_pmap_domain : consistent_pmap_domain num_proc h.ptpool h.pperm h.LAT h.nps

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

theorem LffFrom_some {L : LATable} : ∀ {k m n : Nat}, LffFrom L m k = some n →
    m ≤ n ∧ n < m + k ∧ isLFree (L n) = true
  | 0, _, _, h => by simp [LffFrom] at h
  | k + 1, m, n, h => by
    simp only [LffFrom] at h
    split at h
    · rename_i hf
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.le_refl _, by omega, hf⟩
    · obtain ⟨h1, h2, h3⟩ := LffFrom_some h
      exact ⟨by omega, by omega, h3⟩

theorem Lfirst_free_some {L : LATable} {size n : Nat} (h : Lfirst_free L size = some n) :
    0 < n ∧ n < size ∧ L n = .LATValid false .ATNorm [] := by
  obtain ⟨h1, h2, h3⟩ := LffFrom_some h
  refine ⟨by omega, by omega, ?_⟩
  cases hL : L n with
  | LATUndef => rw [hL] at h3; simp [isLFree] at h3
  | LATValid b t l =>
    rw [hL] at h3
    cases b <;> cases t <;> cases l <;> simp [isLFree] at h3
    rfl

theorem rel_valid {a : ATInfo} {b : Bool} {t : ATType} {l : List LATOwner}
    (h : RelInfo a (.LATValid b t l)) : a = .ATValid b t l.length := by
  cases a with
  | ATUndef => exact absurd h (by simp [RelInfo])
  | ATValid b' t' n => obtain ⟨rfl, rfl, rfl⟩ := h; rfl

/-! ## Mapping a page -/

/-- **`ptInsertPTE0_spec`**: write the entry and add it to the page's owners.
The page must be allocated and not hidden, and the entry not already present. -/
def ptInsertPTE0_spec (num_proc : Nat) (nn vadr padr : Nat) (p : PTPerm) (h : HData) : Option HData :=
  if h.pg = true ∧ h.ipt = true ∧ pt_Arg num_proc nn vadr padr h.nps then
    match h.ptpool nn (PDX vadr) with
    | .PDEValid pi pdt =>
      match h.LAT padr with
      | .LATValid true .ATNorm l =>
        match h.pperm padr with
        | .PGAlloc =>
          match pdt (PTX vadr) with
          | .PTEValid _ _ => none
          | _ =>
            if l.length < 2 ^ 32 - 1 then
              let pt' := setAt (h.ptpool nn) (PDX vadr) (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p)))
              some { h with LAT := setAt h.LAT padr (.LATValid true .ATNorm (.LATO nn (PDX vadr) (PTX vadr) :: l)),
                            ptpool := setAt h.ptpool nn pt' }
            else none
        | _ => none
      | _ => none
    | _ => none
  else none

/-- **`ptInsertPTE_exist`.** -/
theorem ptInsertPTE_exist {num_proc : Nat} {h h' : HData} {d : PTData} {nn vadr padr : Nat} {p : PTPerm}
    (hR : Relate h d) (hpgi : h.pg = h.init) (hPT0 : h.pg = true → h.ipt = true → h.PT = 0)
    (hpib : ∀ pi pdt, h.ptpool nn (PDX vadr) = .PDEValid pi pdt → 0 < pi ∧ pi < 2 ^ 32 - 1)
    (hs : ptInsertPTE0_spec num_proc nn vadr padr p h = some h') :
    ∃ d', ptInsertPTE_spec nn vadr padr p d = some d' ∧ Relate h' d' := by
  unfold ptInsertPTE0_spec at hs
  have hc : h.pg = true ∧ h.ipt = true ∧ pt_Arg num_proc nn vadr padr h.nps := by
    by_cases hh : h.pg = true ∧ h.ipt = true ∧ pt_Arg num_proc nn vadr padr h.nps
    · exact hh
    · rw [if_neg hh] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hpg, hipt, ⟨hn0, hnp, hlo, hhi⟩, hpa0, hpan⟩ := hc
  cases hp : h.ptpool nn (PDX vadr) with
  | PDEID => rw [hp] at hs; cases hs
  | PDEUnPresent => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEValid pi pdt =>
    rw [hp] at hs; simp only at hs
    cases hL : h.LAT padr with
    | LATUndef => rw [hL] at hs; cases hs
    | LATValid b t l =>
      rw [hL] at hs
      cases b <;> cases t <;> simp only at hs <;> try (cases hs)
      cases hq : h.pperm padr with
      | PGUndef => rw [hq] at hs; cases hs
      | PGHide a1 a2 => rw [hq] at hs; cases hs
      | PGAlloc =>
        rw [hq] at hs; simp only at hs
        have hfin : (if l.length < 2 ^ 32 - 1 then
            some ({ h with LAT := setAt h.LAT padr (.LATValid true .ATNorm (.LATO nn (PDX vadr) (PTX vadr) :: l)),
                           ptpool := setAt h.ptpool nn (setAt (h.ptpool nn) (PDX vadr)
                             (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p)))) } : HData)
            else none) = some h' := by
          cases hv : pdt (PTX vadr) with
          | PTEValid a1 a2 => rw [hv] at hs; cases hs
          | PTEUnPresent => rw [hv] at hs; exact hs
          | PTEUndef => rw [hv] at hs; exact hs
        have hll : l.length < 2 ^ 32 - 1 := by
          by_cases hh : l.length < 2 ^ 32 - 1
          · exact hh
          · rw [if_neg hh] at hfin; cases hfin
        rw [if_pos hll] at hfin
        simp only [Option.some.injEq] at hfin
        have hAT : d.AT padr = .ATValid true .ATNorm l.length := rel_valid (by rw [← hL]; exact hR.lat padr)
        have hdp : d.ptpool nn (PDX vadr) = .PDEValid pi pdt := by rw [hR.ptpool]; exact hp
        unfold ptInsertPTE_spec
        rw [if_pos (by rw [hR.init, ← hpgi]; exact hpg),
          if_neg (by rw [hR.PT, hPT0 hpg hipt]; omega), hdp]
        simp only
        rw [if_pos (hpib pi pdt hp), hAT]
        simp only
        rw [if_pos hll]
        refine ⟨_, rfl, ?_⟩
        rw [← hfin]
        refine ⟨fun j => ?_, hR.nps, hR.pperm, hR.init, hR.AC, ?_, hR.idpde, hR.PT, hR.pg, hR.ipt, hR.HP⟩
        · show RelInfo (setAt d.AT padr (.ATValid true .ATNorm (l.length + 1)) j)
            (setAt h.LAT padr (.LATValid true .ATNorm (.LATO nn (PDX vadr) (PTX vadr) :: l)) j)
          by_cases hj : j = padr
          · rw [hj, setAt_eq, setAt_eq]; exact ⟨rfl, rfl, rfl⟩
          · rw [setAt_ne _ _ hj, setAt_ne _ _ hj]; exact hR.lat j
        · show setAt d.ptpool nn (setAt (d.ptpool nn) (PDX vadr) _) = setAt h.ptpool nn _
          rw [hR.ptpool]

/-! ## Allocating a second-level table -/

/-- **`ptAllocPDE0_spec`**. -/
def ptAllocPDE0_spec (num_proc : Nat) (nn vadr : Nat) (h : HData) : Option (HData × Nat) :=
  let c := h.AC nn
  if h.pg = true ∧ h.ipt = true ∧ c.cused = true ∧ pt_Arg' num_proc nn vadr then
    match h.ptpool nn (PDX vadr) with
    | .PDEUnPresent =>
      if c.cusage < c.cquota then
        match Lfirst_free h.LAT h.nps with
        | some pi =>
          let pt' := setAt (h.ptpool nn) (PDX vadr) (.PDEValid pi real_init_PTE)
          some ({ h with HP := free_page pi h.HP, LAT := setAt h.LAT pi (.LATValid true .ATNorm []),
                         pperm := setAt h.pperm pi (.PGHide nn (PDX vadr)),
                         ptpool := setAt h.ptpool nn pt',
                         AC := setAt h.AC nn ⟨c.cquota, c.cusage + 1, c.cparent, c.cchildren, c.cused⟩ }, pi)
        | none => none
      else some (h, 0)
    | _ => none
  else none

/-- **`ptAllocPDE_exist`.** -/
theorem ptAllocPDE_exist {num_proc : Nat} {h h' : HData} {d : PTData} {nn vadr v : Nat} (hR : Relate h d)
    (hpgi : h.pg = h.init) (hPT0 : h.pg = true → h.ipt = true → h.PT = 0) (hnil : LATable_nil h.LAT)
    (hs : ptAllocPDE0_spec num_proc nn vadr h = some (h', v)) :
    ∃ d', ptAllocPDE_spec num_proc nn vadr d = some (d', v) ∧ Relate h' d' := by
  unfold ptAllocPDE0_spec at hs
  simp only at hs
  have hc : h.pg = true ∧ h.ipt = true ∧ (h.AC nn).cused = true ∧ pt_Arg' num_proc nn vadr := by
    by_cases hh : h.pg = true ∧ h.ipt = true ∧ (h.AC nn).cused = true ∧ pt_Arg' num_proc nn vadr
    · exact hh
    · rw [if_neg hh] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hpg, hipt, hused, hn0, hnp, hlo, hhi⟩ := hc
  have hACd : d.AC = h.AC := hR.AC
  unfold ptAllocPDE_spec
  simp only
  rw [if_pos ⟨by rw [hR.init, ← hpgi]; exact hpg, by rw [hR.ipt]; exact hipt, by rw [hACd]; exact hused,
    hn0, hnp, hlo, hhi⟩, if_neg (by rw [hR.PT, hPT0 hpg hipt]; omega), hR.ptpool]
  cases hp : h.ptpool nn (PDX vadr) with
  | PDEID => rw [hp] at hs; cases hs
  | PDEValid a1 a2 => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEUnPresent =>
    rw [hp] at hs; simp only at hs ⊢
    by_cases hlt : (h.AC nn).cusage < (h.AC nn).cquota
    · rw [if_pos hlt] at hs
      rw [if_pos (by rw [hACd]; exact hlt)]
      have hff : first_free d.AT d.nps = Lfirst_free h.LAT h.nps := by
        unfold first_free Lfirst_free; rw [hR.nps]
        exact ff_relate hR.lat hnil _ _
      cases hL : Lfirst_free h.LAT h.nps with
      | none => rw [hL] at hs; cases hs
      | some pi =>
        rw [hL] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        rw [show first_free d.AT d.nps = some pi from hff.trans hL]
        refine ⟨_, rfl, ⟨fun j => ?_, hR.nps, ?_, hR.init, ?_, ?_, hR.idpde, hR.PT, hR.pg, hR.ipt, ?_⟩⟩
        · show RelInfo (setAt d.AT pi (.ATValid true .ATNorm 0) j) (setAt h.LAT pi (.LATValid true .ATNorm []) j)
          by_cases hj : j = pi
          · rw [hj, setAt_eq, setAt_eq]; exact ⟨rfl, rfl, rfl⟩
          · rw [setAt_ne _ _ hj, setAt_ne _ _ hj]; exact hR.lat j
        · show setAt d.pperm pi _ = setAt h.pperm pi _
          rw [hR.pperm]
        · show setAt d.AC nn _ = setAt h.AC nn _
          rw [hACd]
        · show setAt h.ptpool nn _ = setAt h.ptpool nn _
          rfl
        · show free_page pi d.HP = free_page pi h.HP
          rw [hR.HP]
    · rw [if_neg hlt] at hs
      rw [if_neg (by rw [hACd]; exact hlt)]
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      exact ⟨_, rfl, hR⟩

/-- What `ptAllocPDE0_spec` leaves alone, and what it returns. -/
theorem allocPDE0_facts {num_proc : Nat} {h h2 : HData} {nn vadr v : Nat}
    (hs : ptAllocPDE0_spec num_proc nn vadr h = some (h2, v)) :
    h2.pg = h.pg ∧ h2.init = h.init ∧ h2.PT = h.PT ∧ h2.ipt = h.ipt ∧ h2.nps = h.nps ∧
    ((v = 0 ∧ h2 = h) ∨ (0 < v ∧ v < h.nps ∧ h2.ptpool nn (PDX vadr) = .PDEValid v real_init_PTE)) := by
  unfold ptAllocPDE0_spec at hs
  simp only at hs
  by_cases hc : h.pg = true ∧ h.ipt = true ∧ (h.AC nn).cused = true ∧ pt_Arg' num_proc nn vadr
  · rw [if_pos hc] at hs
    cases hp : h.ptpool nn (PDX vadr) with
    | PDEID => rw [hp] at hs; cases hs
    | PDEValid a1 a2 => rw [hp] at hs; cases hs
    | PDEUndef => rw [hp] at hs; cases hs
    | PDEUnPresent =>
      rw [hp] at hs; simp only at hs
      by_cases hlt : (h.AC nn).cusage < (h.AC nn).cquota
      · rw [if_pos hlt] at hs
        cases hL : Lfirst_free h.LAT h.nps with
        | none => rw [hL] at hs; cases hs
        | some pi =>
          rw [hL] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
          obtain ⟨h0, hn, -⟩ := Lfirst_free_some hL
          exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr ⟨h0, hn, pool_get_eq _ _ _ _⟩⟩
      · rw [if_neg hlt] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`ptInsert0_spec`**: `pt_insert` over the owner lists. -/
def ptInsert0_spec (maxpage num_proc : Nat) (nn vadr padr perm : Nat) (h : HData) : Option (HData × Nat) :=
  if h.ipt = true ∧ h.pg = true ∧ pt_Arg num_proc nn vadr padr h.nps then
    match ZtoPerm perm with
    | some p =>
      match h.ptpool nn (PDX vadr) with
      | .PDEValid _ _ =>
        match ptInsertPTE0_spec num_proc nn vadr padr p h with
        | some h' => some (h', 0)
        | none => none
      | .PDEUnPresent =>
        match ptAllocPDE0_spec num_proc nn vadr h with
        | some (h', v) =>
          if v = 0 then some (h', maxpage + 1)
          else
            match ptInsertPTE0_spec num_proc nn vadr padr p h' with
            | some h'' => some (h'', v)
            | none => none
        | none => none
      | _ => none
    | none => none
  else none

/-- **`ptInsert_exist`.** If `pt_insert` over owner lists is defined, so is
`pt_insert` over counts on any related state, with the same result. -/
theorem ptInsert_exist {maxpage num_proc : Nat} (hmp : maxpage ≤ 2 ^ 20) {h h' : HData} {d : PTData}
    {nn vadr padr perm r : Nat} (hR : Relate h d) (hI : HInvI maxpage num_proc h)
    (hs : ptInsert0_spec maxpage num_proc nn vadr padr perm h = some (h', r)) :
    ∃ d', ptInsert_spec maxpage num_proc nn vadr padr perm d = some (d', r) ∧ Relate h' d' := by
  unfold ptInsert0_spec at hs
  have hc : h.ipt = true ∧ h.pg = true ∧ pt_Arg num_proc nn vadr padr h.nps := by
    by_cases hh : h.ipt = true ∧ h.pg = true ∧ pt_Arg num_proc nn vadr padr h.nps
    · exact hh
    · rw [if_neg hh] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hipt, hpg, ⟨hn0, hnp, hlo, hhi⟩, hpa0, hpan⟩ := hc
  have hnpsm := hI.valid_nps
  unfold ptInsert_spec
  rw [if_pos ⟨by rw [hR.init, ← hI.valid_pg_init]; exact hpg, by rw [hR.ipt]; exact hipt,
    by rw [hR.pg]; exact hpg, ⟨hn0, hnp, hlo, hhi⟩, hpa0, by rw [hR.nps]; exact hpan⟩]
  cases hz : ZtoPerm perm with
  | none => rw [hz] at hs; cases hs
  | some p =>
    rw [hz] at hs; simp only at hs ⊢
    rw [hR.ptpool]
    cases hp : h.ptpool nn (PDX vadr) with
    | PDEID => rw [hp] at hs; cases hs
    | PDEUndef => rw [hp] at hs; cases hs
    | PDEValid pi pdt =>
      rw [hp] at hs; simp only at hs ⊢
      cases hi : ptInsertPTE0_spec num_proc nn vadr padr p h with
      | none => rw [hi] at hs; cases hs
      | some h1 =>
        rw [hi] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨d1, hd1, hR1⟩ := ptInsertPTE_exist hR hI.valid_pg_init hI.valid_PT_kern
          (fun pi' pdt' hq => by
            have := (hI.valid_pperm_pmap nn hnp vadr (by omega) pdt' pi' hq).1
            omega) hi
        rw [hd1]; exact ⟨d1, rfl, hR1⟩
    | PDEUnPresent =>
      rw [hp] at hs; simp only at hs ⊢
      cases ha : ptAllocPDE0_spec num_proc nn vadr h with
      | none => rw [ha] at hs; cases hs
      | some pr =>
        obtain ⟨h1, v⟩ := pr
        rw [ha] at hs; simp only at hs
        obtain ⟨d1, hd1, hR1⟩ := ptAllocPDE_exist hR hI.valid_pg_init hI.valid_PT_kern hI.valid_LATable_nil ha
        obtain ⟨e1, e2, e3, e4, e5, hcase⟩ := allocPDE0_facts ha
        rw [hd1]; simp only
        by_cases hv0 : v = 0
        · rw [if_pos hv0] at hs ⊢
          simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
          exact ⟨d1, rfl, hR1⟩
        · rw [if_neg hv0] at hs ⊢
          cases hi : ptInsertPTE0_spec num_proc nn vadr padr p h1 with
          | none => rw [hi] at hs; cases hs
          | some h2 =>
            rw [hi] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
            have hvb : 0 < v ∧ v < h.nps ∧ h1.ptpool nn (PDX vadr) = .PDEValid v real_init_PTE := by
              rcases hcase with ⟨h0, -⟩ | hh
              · exact absurd h0 hv0
              · exact hh
            obtain ⟨d2, hd2, hR2⟩ := ptInsertPTE_exist hR1 (by rw [e1, e2]; exact hI.valid_pg_init)
              (by rw [e1, e3, e4]; exact hI.valid_PT_kern)
              (fun pi' pdt' hq => by
                rw [hvb.2.2] at hq; cases hq
                have := hvb.1; have := hvb.2.1; omega) hi
            rw [hd2]; exact ⟨d2, rfl, hR2⟩

/-! ## Unmapping a page -/

/-- `Lremove`: drop every occurrence of an owner. -/
def Lremove (o : LATOwner) (l : List LATOwner) : List LATOwner := l.filter (fun x => decide (x ≠ o))

theorem remove_len (o : LATOwner) : ∀ l : List LATOwner, (Lremove o l).length + l.count o = l.length
  | [] => rfl
  | x :: xs => by
    have ih := remove_len o xs
    unfold Lremove at ih ⊢
    by_cases hx : x = o
    · subst hx; simp [List.filter_cons, List.count_cons] at ih ⊢; omega
    · simp [List.filter_cons, List.count_cons, hx] at ih ⊢; omega

/-- **`ptRmv0_spec`**: clear the entry and take it out of the page's owners. -/
def ptRmv0_spec (num_proc : Nat) (n vadr : Nat) (h : HData) : Option (HData × Nat) :=
  if h.ipt = true ∧ h.pg = true ∧ pt_Arg' num_proc n vadr then
    match h.ptpool n (PDX vadr) with
    | .PDEValid pi pdt =>
      match pdt (PTX vadr) with
      | .PTEValid padr _ =>
        match h.LAT padr with
        | .LATValid true .ATNorm l =>
          if l.length ≤ 2 ^ 32 - 1 then
            let pt' := setAt (h.ptpool n) (PDX vadr) (.PDEValid pi (setAt pdt (PTX vadr) .PTEUnPresent))
            some ({ h with LAT := setAt h.LAT padr
                             (.LATValid true .ATNorm (Lremove (.LATO n (PDX vadr) (PTX vadr)) l)),
                           ptpool := setAt h.ptpool n pt' }, padr)
          else none
        | _ => none
      | .PTEUnPresent => some (h, 0)
      | .PTEUndef => none
    | _ => none
  else none

/-- **`ptRmv_exist`.** `consistent_pmap_domain` says the entry being removed is
among the page's owners exactly once, so the count goes down by one. -/
theorem ptRmv_exist {maxpage num_proc : Nat} {h h' : HData} {d : PTData} {n vadr r : Nat} (hR : Relate h d)
    (hI : HInvI maxpage num_proc h) (hs : ptRmv0_spec num_proc n vadr h = some (h', r)) :
    ∃ d', ptRmv_spec maxpage num_proc n vadr d = some (d', r) ∧ Relate h' d' := by
  unfold ptRmv0_spec at hs
  have hc : h.ipt = true ∧ h.pg = true ∧ pt_Arg' num_proc n vadr := by
    by_cases hh : h.ipt = true ∧ h.pg = true ∧ pt_Arg' num_proc n vadr
    · exact hh
    · rw [if_neg hh] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨hipt, hpg, hn0, hnp, hlo, hhi⟩ := hc
  have hnpsm := hI.valid_nps
  unfold ptRmv_spec
  rw [if_pos ⟨by rw [hR.init, ← hI.valid_pg_init]; exact hpg, by rw [hR.ipt]; exact hipt,
    by rw [hR.pg]; exact hpg, hn0, hnp, hlo, hhi⟩, if_neg (by rw [hR.PT, hI.valid_PT_kern hpg hipt]; omega),
    hR.ptpool]
  cases hp : h.ptpool n (PDX vadr) with
  | PDEID => rw [hp] at hs; cases hs
  | PDEUnPresent => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEValid pi pdt =>
    rw [hp] at hs; simp only at hs ⊢
    cases hv : pdt (PTX vadr) with
    | PTEUndef => rw [hv] at hs; cases hs
    | PTEUnPresent =>
      rw [hv] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      exact ⟨d, rfl, hR⟩
    | PTEValid padr p0 =>
      rw [hv] at hs; simp only at hs ⊢
      obtain ⟨⟨hpa0, hpan⟩, -, l', hL', hcnt⟩ :=
        hI.valid_pmap_domain n hnp vadr (by omega) pdt pi hp padr p0 hv
      rw [hL'] at hs; simp only at hs
      have hll : l'.length ≤ 2 ^ 32 - 1 := by
        by_cases hh : l'.length ≤ 2 ^ 32 - 1
        · exact hh
        · rw [if_neg hh] at hs; cases hs
      rw [if_pos hll] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      have hrm := remove_len (.LATO n (PDX vadr) (PTX vadr)) l'
      rw [hcnt] at hrm
      have hAT : d.AT padr = .ATValid true .ATNorm l'.length := rel_valid (by rw [← hL']; exact hR.lat padr)
      rw [if_pos ⟨hpa0, by omega⟩, hAT]
      simp only
      rw [if_pos ⟨by omega, hll⟩]
      refine ⟨_, rfl, ⟨fun j => ?_, hR.nps, hR.pperm, hR.init, hR.AC, ?_, hR.idpde, hR.PT, hR.pg, hR.ipt, hR.HP⟩⟩
      · show RelInfo (setAt d.AT padr (.ATValid true .ATNorm (l'.length - 1)) j)
          (setAt h.LAT padr (.LATValid true .ATNorm (Lremove (.LATO n (PDX vadr) (PTX vadr)) l')) j)
        by_cases hj : j = padr
        · rw [hj, setAt_eq, setAt_eq]; exact ⟨rfl, rfl, by omega⟩
        · rw [setAt_ne _ _ hj, setAt_ne _ _ hj]; exact hR.lat j
      · rfl

/-! ## Reserving a page -/

/-- `alloc_spec` keeps the invariant facts. -/
theorem alloc_inv_I {maxpage num_proc : Nat} {h h' : HData} {id i : Nat} (hI : HInvI maxpage num_proc h)
    (hs : alloc_spec id h = some (h', i)) : HInvI maxpage num_proc h' := by
  unfold alloc_spec at hs
  simp only at hs
  by_cases hc : h.pg = true ∧ h.ipt = true ∧ (h.AC id).cused = true
  · rw [if_pos hc] at hs
    by_cases hlt : (h.AC id).cusage < (h.AC id).cquota
    · rw [if_pos hlt] at hs
      cases hL : Lfirst_free h.LAT h.nps with
      | none => rw [hL] at hs; cases hs
      | some p =>
        rw [hL] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨-, -, hLp⟩ := Lfirst_free_some hL
        refine ⟨hI.valid_pg_init, hI.valid_PT_kern, fun j l hj => ?_, hI.valid_nps,
          fun i hi j hj pte pi hq => ?_, fun i hi j hj pte pi hq v p0 hv => ?_⟩
        · have hj' : setAt h.LAT p (.LATValid true .ATNorm []) j = .LATValid false .ATNorm l := hj
          by_cases e : j = p
          · rw [e, setAt_eq] at hj'; cases hj'
          · rw [setAt_ne _ _ e] at hj'; exact hI.valid_LATable_nil j l hj'
        · obtain ⟨o1, o2, o3⟩ := hI.valid_pperm_pmap i hi j hj pte pi hq
          have hne : pi ≠ p := fun e => by rw [e, hLp] at o3; cases o3
          exact ⟨o1, by show setAt h.pperm p .PGAlloc pi = _; rw [setAt_ne _ _ hne]; exact o2,
            by show setAt h.LAT p _ pi = _; rw [setAt_ne _ _ hne]; exact o3⟩
        · obtain ⟨o1, o2, l, o3, o4⟩ := hI.valid_pmap_domain i hi j hj pte pi hq v p0 hv
          have hne : v ≠ p := fun e => by rw [e, hLp] at o3; cases o3
          exact ⟨o1, by show setAt h.pperm p .PGAlloc v = _; rw [setAt_ne _ _ hne]; exact o2,
            l, by show setAt h.LAT p _ v = _; rw [setAt_ne _ _ hne]; exact o3, o4⟩
    · rw [if_neg hlt] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; exact hI
  · rw [if_neg hc] at hs; cases hs

/-- **`ptResv_spec`** of mCertiKOS, over the owner lists. (`MPTNew.ptResv_spec`
is the same over counts.) -/
def ptResv0_spec (maxpage num_proc : Nat) (n vadr perm : Nat) (h : HData) : Option (HData × Nat) :=
  match alloc_spec n h with
  | some (h', b) =>
    if b = 0 then some (h, maxpage + 1)
    else ptInsert0_spec maxpage num_proc n vadr b perm h'
  | none => none

/-- **`ptResv_exist`.** `pt_resv` over owner lists is refined by `pt_resv` over
counts. With `MPTNew.ptResv_triple` this ties the C code of `pt_resv` to
mCertiKOS's top specification of it. -/
theorem ptResv_exist {maxpage num_proc : Nat} (hmp : maxpage ≤ 2 ^ 20) {h h' : HData} {d : PTData}
    {n vadr perm r : Nat} (hR : Relate h d) (hI : HInvI maxpage num_proc h)
    (hs : ptResv0_spec maxpage num_proc n vadr perm h = some (h', r)) :
    ∃ d', ptResv_spec maxpage num_proc n vadr perm d = some (d', r) ∧ Relate h' d' := by
  unfold ptResv0_spec at hs
  cases ha : alloc_spec n h with
  | none => rw [ha] at hs; cases hs
  | some pr =>
    obtain ⟨h1, b⟩ := pr
    rw [ha] at hs; simp only at hs
    obtain ⟨r1, hr1, hR1⟩ := alloc_exist hR hI ha
    unfold ptResv_spec
    rw [hr1]; simp only
    by_cases hb : b = 0
    · rw [if_pos hb] at hs ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      exact ⟨d, rfl, hR⟩
    · rw [if_neg hb] at hs ⊢
      exact ptInsert_exist hmp hR1 (alloc_inv_I hI ha) hs

end PTInitGen
