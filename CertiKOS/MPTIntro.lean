import CertiKOS.MContainerInv

/-!
# mCertiKOS `MPTIntro`: the page-table pool, ported (state and specifications)

The first page-table layer of mCertiKOS: the accessors of the page-table pool
(`PTPool_LOC[NUM_PROC][1024]`), of the identity map (`IDPMap_LOC[1024][1024]`),
and of the second-level tables, which live in the physical pages themselves
and are reached through flat memory (`fload`, `fstore`).

Ported from `layerlib/AuxStateDataType.v`: `PTPerm`, `ZtoPerm`, `PermtoZ`,
`PTEInfo`, `PTE`, `PDE`, `IDPTEInfo`, `PMap`, `PMapPool`.

Ported from `objects/ObjVMMDef.v` and `ObjVMMGetSet.v`: `PDE_Arg`, `PTE_Arg`,
`IDPTE_Arg`, `getPDE_spec`, `setPDE_spec`, `rmvPDE_spec`, `setPDEU_spec`,
`getPTE_spec`, `setPTE_spec`, `rmvPTE_spec`, `setIDPTE_spec`.

Ported from `mm/PTIntroGenDef.v`: `match_PDE`, `match_IDPDE`, `relate_PTE`,
`relate_PMapPool` (together `MatchPT`).

What differs from the sources:

* As before, `ikern` and `ihost` are dropped. `PT` (the current page table),
  `pg` (paging on) and `ipt` are kept, because the specifications test them.
* Flat memory is word-indexed here (`HP : Nat → Option Val`, word `a` is the
  four bytes at `4 * a`). A word that the abstract state hides is `none`:
  `free_page` hides a page when it becomes a page table.
* A directory entry that points to the identity map holds a pointer in
  mCertiKOS. Here it holds the number `ida + i * 4096 + 7`, with `ida` a
  parameter standing for the address of `IDPMap_LOC`.
* `MatchPT.hid` (a page holding a table is hidden from visible flat memory)
  is stated here directly. mCertiKOS gets it from `flatmem_inj` and the
  permission table across two layers.
* `setPT'_spec` and `set_pt` are not ported. They load `CR3`, which needs the
  machine model.

This file has the state, the specifications and the relation to memory. The
C code and its proofs come next.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace MPTIntro

open LockRegion (Region)
open ClightL Ticket
open MALOp MContainer

/-! ## Abstract data (`AuxStateDataType.v`) -/

inductive PTPerm
  | PTP | PTU | PTK (b : Bool)
  deriving DecidableEq

/-- `PT_PERM_P = 1`, `PT_PERM_PTKF = 3`, `PT_PERM_PTKT = 259`, `PT_PERM_PTU = 7`. -/
def ZtoPerm (i : Nat) : Option PTPerm :=
  if i = 1 then some .PTP
  else if i = 3 then some (.PTK false)
  else if i = 259 then some (.PTK true)
  else if i = 7 then some .PTU
  else none

def PermtoZ : PTPerm → Nat
  | .PTP => 1
  | .PTU => 7
  | .PTK false => 3
  | .PTK true => 259

/-- `PermZ_eq`. -/
theorem PermZ_eq {v : Nat} {p : PTPerm} (h : ZtoPerm v = some p) : v = PermtoZ p := by
  unfold ZtoPerm at h
  by_cases h1 : v = 1
  · rw [if_pos h1] at h; cases h; exact h1
  · rw [if_neg h1] at h
    by_cases h3 : v = 3
    · rw [if_pos h3] at h; cases h; exact h3
    · rw [if_neg h3] at h
      by_cases h259 : v = 259
      · rw [if_pos h259] at h; cases h; exact h259
      · rw [if_neg h259] at h
        by_cases h7 : v = 7
        · rw [if_pos h7] at h; cases h; exact h7
        · rw [if_neg h7] at h; cases h

inductive PTEInfo
  | PTEValid (v : Nat) (p : PTPerm)
  | PTEUnPresent
  | PTEUndef

abbrev PTE := Nat → PTEInfo

/-- A directory entry. `PDEValid pi pte`: the second-level table is page `pi`,
with contents `pte`. `PDEID`: the entry points to the identity map. -/
inductive PDE
  | PDEValid (pi : Nat) (pte : PTE)
  | PDEID
  | PDEUnPresent
  | PDEUndef

inductive IDPTEInfo
  | IDPTEValid (p : PTPerm)
  | IDPTEUndef

abbrev PMap := Nat → PDE
abbrev PMapPool := Nat → PMap

/-- `RData` with the page-table pool, the identity map, the current page
table, the paging flags and flat memory. -/
structure PTData extends RData where
  ptpool : PMapPool
  idpde : Nat → Nat → IDPTEInfo
  PT : Nat
  pg : Bool
  ipt : Bool
  HP : Nat → Option Val

/-- `FlatMem.free_page`: the words of page `pi` are no longer visible. -/
def free_page (pi : Nat) (hp : Nat → Option Val) : Nat → Option Val :=
  fun a => if a / 1024 = pi then none else hp a

/-! ## Specifications (`ObjVMMDef.v`, `ObjVMMGetSet.v`) -/

section Specs
variable (num_proc : Nat)

/-- `PDE_Arg`: `0 ≤ n < num_proc` and `0 ≤ i ≤ PDX max_unsigned`. -/
def PDE_Arg (n i : Nat) : Prop := n < num_proc ∧ i < 1024

/-- `PTE_Arg`. -/
def PTE_Arg (n i vadr : Nat) : Prop := PDE_Arg num_proc n i ∧ vadr < 1024

/-- `IDPTE_Arg`. -/
def IDPTE_Arg (i vadr : Nat) : Prop := i < 1024 ∧ vadr < 1024

instance (n i : Nat) : Decidable (PDE_Arg num_proc n i) := by unfold PDE_Arg; exact inferInstance
instance (n i v : Nat) : Decidable (PTE_Arg num_proc n i v) := by unfold PTE_Arg; exact inferInstance
instance (i v : Nat) : Decidable (IDPTE_Arg i v) := by unfold IDPTE_Arg; exact inferInstance

/-- The page a directory entry points to, or 0 if it is not present. -/
def getPDE_spec (n i : Nat) (d : PTData) : Option Nat :=
  if d.init = true ∧ d.ipt = true ∧ PDE_Arg num_proc n i then
    match d.ptpool n i with
    | .PDEValid pi _ => some pi
    | .PDEUnPresent => some 0
    | _ => none
  else none

/-- Point a directory entry to the identity map. Only before paging is on. -/
def setPDE_spec (n i : Nat) (d : PTData) : Option PTData :=
  if d.pg = false ∧ d.init = true ∧ d.ipt = true ∧ PDE_Arg num_proc n i then
    some { d with ptpool := setAt d.ptpool n (setAt (d.ptpool n) i .PDEID) }
  else none

/-- Remove a directory entry. If it held a table, the page is the kernel's
to free again (`PGHide` becomes `PGAlloc`). -/
def rmvPDE_spec (n i : Nat) (d : PTData) : Option PTData :=
  if d.init = true ∧ d.ipt = true ∧ PDE_Arg num_proc n i then
    let pt' := setAt (d.ptpool n) i .PDEUnPresent
    if n = d.PT ∧ d.pg = true then none
    else
      match d.ptpool n i with
      | .PDEValid pi _ =>
        match d.pperm pi with
        | .PGHide _ _ =>
          some { d with pperm := setAt d.pperm pi .PGAlloc, ptpool := setAt d.ptpool n pt' }
        | _ => none
      | _ => some { d with ptpool := setAt d.ptpool n pt' }
  else none

/-- Install page `pi` as the second-level table of entry `i`. The page must be
allocated and unmapped (`PGAlloc`). It becomes hidden (`PGHide`), and its
contents leave the visible flat memory. -/
def setPDEU_spec (n i pi : Nat) (d : PTData) : Option PTData :=
  if d.init = true ∧ d.ipt = true ∧ PDE_Arg num_proc n i then
    if n = d.PT then none
    else if 0 < pi ∧ pi < d.nps then
      match d.pperm pi with
      | .PGAlloc =>
        let pt' := setAt (d.ptpool n) i (.PDEValid pi (fun _ => .PTEUndef))
        some { d with HP := free_page pi d.HP, pperm := setAt d.pperm pi (.PGHide n i),
                      ptpool := setAt d.ptpool n pt' }
      | _ => none
    else none
  else none

/-- Read a second-level entry: `padr * PgSize + perm`, or 0 if not present. -/
def getPTE_spec (n i vadr : Nat) (d : PTData) : Option Nat :=
  if d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr then
    match d.ptpool n i with
    | .PDEValid _ pdt =>
      match pdt vadr with
      | .PTEValid padr p => some (padr * 4096 + PermtoZ p)
      | .PTEUnPresent => some 0
      | .PTEUndef => none
    | _ => none
  else none

/-- Write a second-level entry. Not allowed on the current page table. -/
def setPTE_spec (n i vadr padr perm : Nat) (d : PTData) : Option PTData :=
  if d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr then
    match ZtoPerm perm with
    | some p =>
      if n = d.PT then none
      else if 0 < padr ∧ padr < d.nps then
        match d.ptpool n i with
        | .PDEValid pi pdt =>
          let pt' := setAt (d.ptpool n) i (.PDEValid pi (setAt pdt vadr (.PTEValid padr p)))
          some { d with ptpool := setAt d.ptpool n pt' }
        | _ => none
      else none
    | none => none
  else none

/-- Clear a second-level entry. -/
def rmvPTE_spec (n i vadr : Nat) (d : PTData) : Option PTData :=
  if d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr then
    if n = d.PT then none
    else
      match d.ptpool n i with
      | .PDEValid pi pdt =>
        let pt' := setAt (d.ptpool n) i (.PDEValid pi (setAt pdt vadr .PTEUnPresent))
        some { d with ptpool := setAt d.ptpool n pt' }
      | _ => none
  else none

/-- Set an entry of the identity map. Only before paging is on. -/
def setIDPTE_spec (i vadr perm : Nat) (d : PTData) : Option PTData :=
  if d.pg = false ∧ d.init = true ∧ d.ipt = true ∧ IDPTE_Arg i vadr then
    match ZtoPerm perm with
    | some p => some { d with idpde := setAt d.idpde i (setAt (d.idpde i) vadr (.IDPTEValid p)) }
    | none => none
  else none

end Specs

/-! ## The page tables in the region (`PTIntroGenDef.v`) -/

/-- `match_PDE`. `ida` stands for the address of the identity map. -/
def MatchPDE (pperm : Nat → PPgInfo) (ida : Nat) (x : PDE) (v : Val) (n i : Nat) : Prop :=
  match x with
  | .PDEUndef => True
  | .PDEUnPresent => v = 0
  | .PDEID => v.toNat = ida + i * 4096 + 7
  | .PDEValid pi _ => v.toNat = pi * 4096 + 7 ∧ pperm pi = .PGHide n i

/-- `relate_PTE`: a second-level entry and its word in flat memory. -/
def RelPTE : PTEInfo → Val → Prop
  | .PTEUndef, _ => True
  | .PTEUnPresent, v => v = 0
  | .PTEValid padr p, v => v.toNat = padr * 4096 + PermtoZ p

/-- `match_IDPDE`. -/
def MatchIDPTE : IDPTEInfo → Val → Nat → Nat → Prop
  | .IDPTEUndef, _, _, _ => True
  | .IDPTEValid p, v, i, j => v.toNat = (i * 1024 + j) * 4096 + PermtoZ p

/-- The page-table pool at cell `pb`, the identity map at `ib`, flat memory at
`fb`. Together with `MContainer.MatchMM` this is the memory-management region. -/
structure MatchPT (num_proc pb ib fb ida : Nat) (d : PTData) (b : Region) : Prop where
  /-- `match_PMapPool` -/
  pool : ∀ n i, n < num_proc → i < 1024 →
    MatchPDE d.pperm ida (d.ptpool n i) (b (pb + n * 1024 + i)) n i
  /-- `match_IDPMap` -/
  idp : ∀ i j, i < 1024 → j < 1024 → MatchIDPTE (d.idpde i j) (b (ib + i * 1024 + j)) i j
  /-- `relate_PMapPool`: the second-level tables are in the pages themselves. -/
  pte : ∀ n i pi pdx, n < num_proc → i < 1024 → d.ptpool n i = .PDEValid pi pdx →
    ∀ vadr, vadr < 1024 → RelPTE (pdx vadr) (b (fb + pi * 1024 + vadr))
  /-- `flatmem_inj`: visible flat memory is what the region holds. -/
  hp : ∀ a v, d.HP a = some v → b (fb + a) = v
  /-- A page that holds a second-level table is hidden from visible flat memory. -/
  hid : ∀ n i pi pdx, n < num_proc → i < 1024 → d.ptpool n i = .PDEValid pi pdx →
    ∀ a, a / 1024 = pi → d.HP a = none

/-! ## The C code of the read accessors (`MContainerCSource.v`) -/

open LockArray (APrim lkE)
open LockRegion (RLog REnv)
open LockRegionCPU KernFrame Layer

/-- The whole memory-management region at this layer. -/
structure MatchAll (maxpage num_id cb num_proc pb ib fb ida : Nat) (d : PTData) (b : Region) : Prop where
  mm : MatchMM maxpage num_id cb d.toRData b
  pt : MatchPT num_proc pb ib fb ida d b

/-- `&PTPool_LOC[n][i]` -/
def pdeE (pb : Nat) : Expr :=
  .bin .add (.bin .add (.const (BitVec.ofNat 32 pb)) (.bin .mul (.var "n") (.const 1024))) (.var "i")

/-- `get_PDE(n, i)`: `return (unsigned int)PTPool_LOC[n][i] / 4096;` -/
def getPDES (pb : Nat) : Stmt APrim :=
  .seq (.call "r" .pull [lkE, pdeE pb]) (.assign "r" (.bin .div (.var "r") (.const 4096)))

/-- `get_PTE(n, i, vadr)`:
`offset = ((unsigned int)PTPool_LOC[n][i] - PT_PERM_PTU) / 4096; return fload(offset * 1024 + vadr);` -/
def getPTES (pb fb : Nat) : Stmt APrim :=
  .seq (.call "o" .pull [lkE, pdeE pb])
    (.seq (.assign "o" (.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096)))
      (.call "r" .pull [lkE, .bin .add (.bin .add (.const (BitVec.ofNat 32 fb))
        (.bin .mul (.var "o") (.const 1024))) (.var "vadr")]))

theorem pde_ix {pb num_proc n i : Nat} (hpb : pb + num_proc * 1024 < 2 ^ 32) (hn : n < num_proc)
    (hi : i < 1024) {σ : Locals} (h1 : σ "n" = BitVec.ofNat 32 n) (h2 : σ "i" = BitVec.ofNat 32 i) :
    ((pdeE pb).eval σ).toNat = pb + n * 1024 + i := by
  show (BitVec.ofNat 32 pb + σ "n" * 1024 + σ "i").toNat = _
  rw [h1, h2]
  simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

section Read
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **`get_PDE` refines `getPDE_spec`.** -/
theorem getPDE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hpb : pb + num_proc * 1024 < 2 ^ 32) (n i : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => False)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "i" = BitVec.ofNat 32 i ∧
        ∃ v, getPDE_spec num_proc n i d = some v)
      (getPDES pb)
      (fun _ d σ' d' => d' = d ∧ ∃ v, getPDE_spec num_proc n i d = some v ∧ σ' "r" = BitVec.ofNat 32 v) := by
  intro σ l b d hlk hcs hM ⟨hn, hi, v, hs⟩
  have hs0 := hs
  unfold getPDE_spec at hs
  have hc : d.init = true ∧ d.ipt = true ∧ PDE_Arg num_proc n i := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ PDE_Arg num_proc n i
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨-, -, hnp, hi1⟩ := hc
  have hix := pde_ix hpb hnp hi1 hn hi
  have hrd := cs1_rd (εR := εR) hcs hlk "r" (pdeE pb)
  rw [hix] at hrd
  have hm := hM.pt.pool n i hnp hi1
  have hval : b (pb + n * 1024 + i) / 4096 = BitVec.ofNat 32 v := by
    cases hp : d.ptpool n i with
    | PDEValid pi pte =>
      rw [hp] at hs hm; simp only [Option.some.injEq] at hs; subst hs
      obtain ⟨hv, -⟩ := hm
      have hlt := (b (pb + n * 1024 + i)).isLt
      exact val_of_toNat (by rw [BitVec.toNat_udiv, hv]; show (pi * 4096 + 7) / 4096 = pi; omega) (by omega)
    | PDEUnPresent =>
      rw [hp] at hs hm; simp only [Option.some.injEq] at hs; subst hs
      rw [show b (pb + n * 1024 + i) = 0 from hm]; rfl
    | PDEID => rw [hp] at hs; cases hs
    | PDEUndef => rw [hp] at hs; cases hs
  have ha := Runs.assign (P := rprimsA εR c) (σ := σ.set "r" (b (pb + n * 1024 + i))) (l := l) "r"
    (.bin .div (.var "r") (.const 4096))
  have e : (Expr.bin .div (.var "r") (.const 4096)).eval (σ.set "r" (b (pb + n * 1024 + i))) =
      BitVec.ofNat 32 v := by
    show (σ.set "r" (b (pb + n * 1024 + i))) "r" / 4096 = _
    rw [Locals.set_same]; exact hval
  rw [e] at ha
  exact ⟨_, l, b, d, Runs.seq hrd ha, hcs, hM, by simp [Locals.set], fun _ _ => rfl, rfl, v, hs0, by simp⟩

/-- **`get_PTE` refines `getPTE_spec`.** The entry is read from the page that
holds the second-level table, through flat memory. -/
theorem getPTE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hpb : pb + num_proc * 1024 < 2 ^ 32)
    (hfb : fb + 2 ^ 30 ≤ 2 ^ 32) (n i vadr : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => False)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "i" = BitVec.ofNat 32 i ∧
        σ "vadr" = BitVec.ofNat 32 vadr ∧ ∃ v, getPTE_spec num_proc n i vadr d = some v)
      (getPTES pb fb)
      (fun _ d σ' d' => d' = d ∧ ∃ v, getPTE_spec num_proc n i vadr d = some v ∧
        σ' "r" = BitVec.ofNat 32 v) := by
  intro σ l b d hlk hcs hM ⟨hn, hi, hva, v, hs⟩
  have hs0 := hs
  unfold getPTE_spec at hs
  have hc : d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨-, -, ⟨hnp, hi1⟩, hv1⟩ := hc
  have hix := pde_ix hpb hnp hi1 hn hi
  have hrd := cs1_rd (εR := εR) hcs hlk "o" (pdeE pb)
  rw [hix] at hrd
  have hm := hM.pt.pool n i hnp hi1
  cases hp : d.ptpool n i with
  | PDEID => rw [hp] at hs; cases hs
  | PDEUnPresent => rw [hp] at hs; cases hs
  | PDEUndef => rw [hp] at hs; cases hs
  | PDEValid pi pdt =>
    rw [hp] at hs hm
    simp only at hs
    obtain ⟨hv, -⟩ := hm
    have hlt := (b (pb + n * 1024 + i)).isLt
    have hpi : pi < 2 ^ 20 := by omega
    have hrel := hM.pt.pte n i pi pdt hnp hi1 hp vadr hv1
    -- the offset
    let σ1 := σ.set "o" (b (pb + n * 1024 + i))
    let σ2 := σ1.set "o" (BitVec.ofNat 32 pi)
    have ha : Runs (rprimsA εR c) (.assign "o" (.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096)))
        σ1 l σ2 l := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l) "o"
        (.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096))
      have e : (Expr.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096)).eval σ1 =
          BitVec.ofNat 32 pi := by
        show (σ1 "o" - 7) / 4096 = _
        have : σ1 "o" = b (pb + n * 1024 + i) := by simp [σ1]
        rw [this]
        refine val_of_toNat ?_ (by omega)
        rw [BitVec.toNat_udiv, BitVec.toNat_sub, hv]
        show (2 ^ 32 - 7 + (pi * 4096 + 7)) % 2 ^ 32 / 4096 = pi
        omega
      rw [e] at h; exact h
    have hrd2 := cs1_rd (εR := εR) hcs (σ := σ2) (by simpa [σ2, σ1, Locals.set] using hlk) "r"
      (.bin .add (.bin .add (.const (BitVec.ofNat 32 fb)) (.bin .mul (.var "o") (.const 1024))) (.var "vadr"))
    have hix2 : ((Expr.bin .add (.bin .add (.const (BitVec.ofNat 32 fb))
        (.bin .mul (.var "o") (.const 1024))) (.var "vadr")).eval σ2).toNat = fb + pi * 1024 + vadr := by
      show (BitVec.ofNat 32 fb + σ2 "o" * 1024 + σ2 "vadr").toNat = _
      have h1 : σ2 "o" = BitVec.ofNat 32 pi := by simp [σ2]
      have h2 : σ2 "vadr" = BitVec.ofNat 32 vadr := by simp [σ2, σ1, Locals.set, hva]
      rw [h1, h2]
      simp [BitVec.toNat_add, BitVec.toNat_mul]; omega
    rw [hix2] at hrd2
    have hval : b (fb + pi * 1024 + vadr) = BitVec.ofNat 32 v := by
      have hlt2 := (b (fb + pi * 1024 + vadr)).isLt
      cases hq : pdt vadr with
      | PTEValid padr p =>
        rw [hq] at hs hrel; simp only [Option.some.injEq] at hs; subst hs
        exact val_of_toNat hrel (by rw [← show (b (fb + pi * 1024 + vadr)).toNat = _ from hrel]; exact hlt2)
      | PTEUnPresent =>
        rw [hq] at hs hrel; simp only [Option.some.injEq] at hs; subst hs; exact hrel
      | PTEUndef => rw [hq] at hs; cases hs
    rw [hval] at hrd2
    exact ⟨_, l, b, d, Runs.seq hrd (Runs.seq ha hrd2), hcs, hM, by simp [σ2, σ1, Locals.set],
      fun _ _ => rfl, rfl, v, hs0, by simp⟩

end Read

/-! ## Updating an entry keeps the relation -/

open LockRegion (setCell)

/-- Where the tables sit in the region, bottom up: allocation table,
containers, page-table pool, identity map, flat memory. -/
structure Layout (maxpage num_id cb num_proc pb ib fb : Nat) : Prop where
  hcb : 3 * maxpage < cb
  hpb : cb + 5 * num_id ≤ pb
  hib : pb + num_proc * 1024 ≤ ib
  hfb : ib + 2 ^ 20 ≤ fb
  hend : fb + 2 ^ 30 ≤ 2 ^ 32

theorem sc_eq (b : Region) (j : Nat) (v : Val) : setCell b j v j = v := by simp [setCell]

theorem sc_ne (b : Region) {j k : Nat} (v : Val) (h : k ≠ j) : setCell b j v k = b k := by
  simp [setCell, h]

theorem pool_get_eq (P : PMapPool) (n i : Nat) (x : PDE) : setAt P n (setAt (P n) i x) n i = x := by
  simp [setAt]

theorem pool_get_ne (P : PMapPool) {n i n' i' : Nat} (x : PDE) (h : ¬ (n' = n ∧ i' = i)) :
    setAt P n (setAt (P n) i x) n' i' = P n' i' := by
  unfold setAt
  by_cases hn : n' = n
  · subst hn
    by_cases hi : i' = i
    · exact absurd ⟨rfl, hi⟩ h
    · simp [hi]
  · simp [hn]

section Update
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- Writes above the containers leave the allocation table and containers matched. -/
theorem mm_frame (hL : Layout maxpage num_id cb num_proc pb ib fb) {d d' : RData} {b b' : Region}
    (h : MatchMM maxpage num_id cb d b) (hAT : d'.AT = d.AT) (hn : d'.nps = d.nps) (hAC : d'.AC = d.AC)
    (hb : ∀ k, k < pb → b' k = b k) : MatchMM maxpage num_id cb d' b' := by
  have := hL.hcb; have := hL.hpb
  refine ⟨⟨fun j hj => ?_, ?_⟩, fun j hj => ?_⟩
  · rw [hAT, hb _ (by omega), hb _ (by omega), hb _ (by omega)]; exact h.mAT.mat j hj
  · rw [hn, hb _ (by omega)]; exact h.mAT.mnps
  · rw [hAC, hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]
    exact h.mAC j hj

/-- Two present directory entries never share a page: the permission table
names the one entry that owns it. -/
theorem pde_unique {d : PTData} {b : Region} (hM : MatchPT num_proc pb ib fb ida d b) {n i n' i' pi : Nat}
    {pdx pdx' : PTE} (hn : n < num_proc) (hi : i < 1024) (hn' : n' < num_proc) (hi' : i' < 1024)
    (h : d.ptpool n i = .PDEValid pi pdx) (h' : d.ptpool n' i' = .PDEValid pi pdx') : n' = n ∧ i' = i := by
  have a := hM.pool n i hn hi; rw [h] at a
  have a' := hM.pool n' i' hn' hi'; rw [h'] at a'
  have e := a.2.symm.trans a'.2
  cases e; exact ⟨rfl, rfl⟩

/-- **Replacing a directory entry.** The new entry `x` with word `w`, a new
permission table and a new visible flat memory keep the relation, if they
agree with the old ones away from this entry. -/
theorem pool_update (hL : Layout maxpage num_id cb num_proc pb ib fb) {d : PTData} {b : Region}
    (hM : MatchPT num_proc pb ib fb ida d b) {n i : Nat} (hn : n < num_proc) (hi : i < 1024) (x : PDE)
    (w : Val) (pperm' : Nat → PPgInfo) (HP' : Nat → Option Val)
    (hx : MatchPDE pperm' ida x w n i)
    (hxpte : ∀ pi pdx, x = .PDEValid pi pdx → ∀ vadr, vadr < 1024 → RelPTE (pdx vadr) (b (fb + pi * 1024 + vadr)))
    (hxhid : ∀ pi pdx, x = .PDEValid pi pdx → ∀ a, a / 1024 = pi → HP' a = none)
    (hpp : ∀ n' i' pi' pdx', ¬ (n' = n ∧ i' = i) → n' < num_proc → i' < 1024 →
      d.ptpool n' i' = .PDEValid pi' pdx' → pperm' pi' = d.pperm pi')
    (hHP : ∀ a v, HP' a = some v → d.HP a = some v) :
    MatchPT num_proc pb ib fb ida
      { d with pperm := pperm', HP := HP', ptpool := setAt d.ptpool n (setAt (d.ptpool n) i x) }
      (setCell b (pb + n * 1024 + i) w) := by
  have := hL.hib; have := hL.hfb
  refine ⟨fun n' i' hn' hi' => ?_, fun i' j hi' hj => ?_, fun n' i' pi' pdx' hn' hi' hp vadr hv => ?_,
    fun a v hav => ?_, fun n' i' pi' pdx' hn' hi' hp a ha => ?_⟩
  · show MatchPDE pperm' ida (setAt d.ptpool n (setAt (d.ptpool n) i x) n' i')
      (setCell b (pb + n * 1024 + i) w (pb + n' * 1024 + i')) n' i'
    by_cases h : n' = n ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h; rw [pool_get_eq, sc_eq]; exact hx
    · rw [pool_get_ne _ _ h, sc_ne _ _ (by omega)]
      have old := hM.pool n' i' hn' hi'
      cases hq : d.ptpool n' i' with
      | PDEValid pi' pdx' =>
        rw [hq] at old; exact ⟨old.1, (hpp n' i' pi' pdx' h hn' hi' hq).trans old.2⟩
      | PDEID => rw [hq] at old; exact old
      | PDEUnPresent => rw [hq] at old; exact old
      | PDEUndef => trivial
  · show MatchIDPTE (d.idpde i' j) (setCell b (pb + n * 1024 + i) w (ib + i' * 1024 + j)) i' j
    rw [sc_ne _ _ (by omega)]; exact hM.idp i' j hi' hj
  · have hp' : setAt d.ptpool n (setAt (d.ptpool n) i x) n' i' = .PDEValid pi' pdx' := hp
    rw [sc_ne _ _ (by omega)]
    by_cases h : n' = n ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h; rw [pool_get_eq] at hp'; exact hxpte pi' pdx' hp' vadr hv
    · rw [pool_get_ne _ _ h] at hp'; exact hM.pte n' i' pi' pdx' hn' hi' hp' vadr hv
  · rw [sc_ne _ _ (by omega)]; exact hM.hp a v (hHP a v hav)
  · have hp' : setAt d.ptpool n (setAt (d.ptpool n) i x) n' i' = .PDEValid pi' pdx' := hp
    show HP' a = none
    by_cases h : n' = n ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h; rw [pool_get_eq] at hp'; exact hxhid pi' pdx' hp' a ha
    · rw [pool_get_ne _ _ h] at hp'
      have old := hM.hid n' i' pi' pdx' hn' hi' hp' a ha
      cases hh : HP' a with
      | none => rfl
      | some v => rw [hHP a v hh] at old; cases old

/-- **Writing a second-level entry.** The word `w` for the new entry `x` goes
into the page that holds the table. -/
theorem pte_update (hL : Layout maxpage num_id cb num_proc pb ib fb) {d : PTData} {b : Region}
    (hM : MatchPT num_proc pb ib fb ida d b) {n i pi : Nat} {pdt : PTE} (hn : n < num_proc) (hi : i < 1024)
    (hp : d.ptpool n i = .PDEValid pi pdt) {vadr : Nat} (hv : vadr < 1024) (x : PTEInfo) (w : Val)
    (hx : RelPTE x w) :
    MatchPT num_proc pb ib fb ida
      { d with ptpool := setAt d.ptpool n (setAt (d.ptpool n) i (.PDEValid pi (setAt pdt vadr x))) }
      (setCell b (fb + pi * 1024 + vadr) w) := by
  have := hL.hib; have := hL.hfb
  refine ⟨fun n' i' hn' hi' => ?_, fun i' j hi' hj => ?_, fun n' i' pi' pdx' hn' hi' hp2 vadr' hv' => ?_,
    fun a v hav => ?_, fun n' i' pi' pdx' hn' hi' hp2 a ha => ?_⟩
  · show MatchPDE d.pperm ida (setAt d.ptpool n (setAt (d.ptpool n) i _) n' i')
      (setCell b (fb + pi * 1024 + vadr) w (pb + n' * 1024 + i')) n' i'
    rw [sc_ne _ _ (by omega)]
    by_cases h : n' = n ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h; rw [pool_get_eq]
      have old := hM.pool n' i' hn hi; rw [hp] at old; exact old
    · rw [pool_get_ne _ _ h]; exact hM.pool n' i' hn' hi'
  · show MatchIDPTE (d.idpde i' j) (setCell b (fb + pi * 1024 + vadr) w (ib + i' * 1024 + j)) i' j
    rw [sc_ne _ _ (by omega)]; exact hM.idp i' j hi' hj
  · have hp' : setAt d.ptpool n (setAt (d.ptpool n) i (.PDEValid pi (setAt pdt vadr x))) n' i' =
        .PDEValid pi' pdx' := hp2
    by_cases h : n' = n ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h
      rw [pool_get_eq] at hp'
      cases hp'
      by_cases hvv : vadr' = vadr
      · rw [hvv, setAt_eq, sc_eq]; exact hx
      · rw [setAt_ne _ _ hvv, sc_ne _ _ (by omega)]; exact hM.pte n' i' pi pdt hn hi hp vadr' hv'
    · rw [pool_get_ne _ _ h] at hp'
      have hne : pi' ≠ pi := fun e => h (pde_unique hM hn hi hn' hi' hp (e ▸ hp'))
      rw [sc_ne _ _ (by omega)]; exact hM.pte n' i' pi' pdx' hn' hi' hp' vadr' hv'
  · have hh := hM.hid n i pi pdt hn hi hp
    have hne : a ≠ pi * 1024 + vadr := fun e => by
      have := hh a (by rw [e]; omega); rw [this] at hav; cases (hav : (none : Option Val) = some v)
    rw [sc_ne _ _ (by omega)]; exact hM.hp a v hav
  · have hp' : setAt d.ptpool n (setAt (d.ptpool n) i (.PDEValid pi (setAt pdt vadr x))) n' i' =
        .PDEValid pi' pdx' := hp2
    show d.HP a = none
    by_cases h : n' = n ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h
      rw [pool_get_eq] at hp'; cases hp'
      exact hM.hid n' i' pi pdt hn hi hp a ha
    · rw [pool_get_ne _ _ h] at hp'; exact hM.hid n' i' pi' pdx' hn' hi' hp' a ha

end Update

/-! ## The C code of the write accessors (`MContainerCSource.v`) -/

/-- `&flat[offset * 1024 + vadr]` -/
def pteE (fb : Nat) : Expr :=
  .bin .add (.bin .add (.const (BitVec.ofNat 32 fb)) (.bin .mul (.var "o") (.const 1024))) (.var "vadr")

/-- `offset = ((unsigned int)PTPool_LOC[n][i] - PT_PERM_PTU) / 4096; fstore(offset * 1024 + vadr, w);` -/
def pteStoreS (pb fb : Nat) (we : Expr) : Stmt APrim :=
  .seq (.call "o" .pull [lkE, pdeE pb])
    (.seq (.assign "o" (.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096)))
      (.call "_" .push [lkE, pteE fb, we]))

/-- `set_PTE(n, i, vadr, padr, perm)`: `fstore(offset * 1024 + vadr, padr * 4096 + perm);` -/
def setPTES (pb fb : Nat) : Stmt APrim :=
  pteStoreS pb fb (.bin .add (.bin .mul (.var "padr") (.const 4096)) (.var "perm"))

/-- `rmv_PTE(n, i, vadr)`: `fstore(offset * 1024 + vadr, 0);` -/
def rmvPTES (pb fb : Nat) : Stmt APrim := pteStoreS pb fb (.const 0)

/-- `set_PDEU(n, i, pi)`: `PTPool_LOC[n][i] = pi * 4096 + PT_PERM_PTU;` -/
def setPDEUS (pb : Nat) : Stmt APrim :=
  .call "_" .push [lkE, pdeE pb, .bin .add (.bin .mul (.var "pi") (.const 4096)) (.const 7)]

/-- `rmv_PDE(n, i)`: `PTPool_LOC[n][i] = PT_PERM_UP;` -/
def rmvPDES (pb : Nat) : Stmt APrim := .call "_" .push [lkE, pdeE pb, .const 0]

/-- `set_PDE(n, i)`: `PTPool_LOC[n][i] = (char * )IDPMap_LOC[i] + PT_PERM_PTU;` -/
def setPDES (pb ida : Nat) : Stmt APrim :=
  .call "_" .push [lkE, pdeE pb,
    .bin .add (.bin .add (.const (BitVec.ofNat 32 ida)) (.bin .mul (.var "i") (.const 4096))) (.const 7)]

section Write
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- The run of a second-level store. -/
theorem pteStore_run (εR : REnv) {c : CPU} {i0 : Nat} (hL : Layout maxpage num_id cb num_proc pb ib fb)
    {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) {d : PTData}
    (hM : MatchPT num_proc pb ib fb ida d b) {n i vadr pi : Nat} {pdt : PTE} (hnp : n < num_proc)
    (hi1 : i < 1024) (hv1 : vadr < 1024) (hn : σ "n" = BitVec.ofNat 32 n) (hi : σ "i" = BitVec.ofNat 32 i)
    (hva : σ "vadr" = BitVec.ofNat 32 vadr) (hp : d.ptpool n i = .PDEValid pi pdt) (we : Expr) {w : Val}
    (hw : ∀ τ : Locals, (∀ z, z ≠ "o" → τ z = σ z) → we.eval τ = w) :
    ∃ σ' l', Runs (rprimsA εR c) (pteStoreS pb fb we) σ l σ' l' ∧
      CS1 c i0 l' (setCell b (fb + pi * 1024 + vadr) w) ∧ σ' "lk" = σ "lk" := by
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb
  have hix := pde_ix (pb := pb) (num_proc := num_proc) (by omega) hnp hi1 hn hi
  have hrd := cs1_rd (εR := εR) hcs hlk "o" (pdeE pb)
  rw [hix] at hrd
  have hm := hM.pool n i hnp hi1
  rw [hp] at hm
  obtain ⟨hv, -⟩ := hm
  have hlt := (b (pb + n * 1024 + i)).isLt
  have hpi : pi < 2 ^ 20 := by omega
  let σ1 := σ.set "o" (b (pb + n * 1024 + i))
  let σ2 := σ1.set "o" (BitVec.ofNat 32 pi)
  have ha : Runs (rprimsA εR c) (.assign "o" (.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096)))
      σ1 l σ2 l := by
    have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l) "o"
      (.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096))
    have e : (Expr.bin .div (.bin .sub (.var "o") (.const 7)) (.const 4096)).eval σ1 =
        BitVec.ofNat 32 pi := by
      show (σ1 "o" - 7) / 4096 = _
      have : σ1 "o" = b (pb + n * 1024 + i) := by simp [σ1]
      rw [this]
      refine val_of_toNat ?_ (by omega)
      rw [BitVec.toNat_udiv, BitVec.toNat_sub, hv]
      show (2 ^ 32 - 7 + (pi * 4096 + 7)) % 2 ^ 32 / 4096 = pi
      omega
    rw [e] at h; exact h
  obtain ⟨l', hwr, hc'⟩ := cs1_wr (εR := εR) hcs (σ := σ2) (by simpa [σ2, σ1, Locals.set] using hlk)
    (pteE fb) we
  have hix2 : ((pteE fb).eval σ2).toNat = fb + pi * 1024 + vadr := by
    show (BitVec.ofNat 32 fb + σ2 "o" * 1024 + σ2 "vadr").toNat = _
    have h1 : σ2 "o" = BitVec.ofNat 32 pi := by simp [σ2]
    have h2 : σ2 "vadr" = BitVec.ofNat 32 vadr := by simp [σ2, σ1, Locals.set, hva]
    rw [h1, h2]
    simp [BitVec.toNat_add, BitVec.toNat_mul]; omega
  have hwv : we.eval σ2 = w := hw σ2 (fun z hz => by simp [σ2, σ1, Locals.set, hz])
  rw [hix2, hwv] at hc'
  exact ⟨_, l', Runs.seq hrd (Runs.seq ha hwr), hc', by simp [σ2, σ1, Locals.set]⟩

theorem perm_le (p : PTPerm) : PermtoZ p ≤ 259 := by
  cases p with
  | PTP => decide
  | PTU => decide
  | PTK b => cases b <;> decide

/-- **`set_PTE` refines `setPTE_spec`.** -/
theorem setPTE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (n i vadr padr perm : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "i" = BitVec.ofNat 32 i ∧
        σ "vadr" = BitVec.ofNat 32 vadr ∧ σ "padr" = BitVec.ofNat 32 padr ∧
        σ "perm" = BitVec.ofNat 32 perm ∧ d.nps ≤ 2 ^ 20 ∧
        ∃ d1, setPTE_spec num_proc n i vadr padr perm d = some d1)
      (setPTES pb fb)
      (fun _ d _ d' => setPTE_spec num_proc n i vadr padr perm d = some d') := by
  intro σ l b d hlk hcs hM ⟨hn, hi, hva, hpa, hpe, hnps, d1, hs⟩
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb
  have hs0 := hs
  unfold setPTE_spec at hs
  have hc : d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨-, -, ⟨hnp, hi1⟩, hv1⟩ := hc
  cases hz : ZtoPerm perm with
  | none => rw [hz] at hs; cases hs
  | some p =>
    rw [hz] at hs; simp only at hs
    by_cases hPT : n = d.PT
    · rw [if_pos hPT] at hs; cases hs
    · rw [if_neg hPT] at hs
      by_cases hpr : 0 < padr ∧ padr < d.nps
      · rw [if_pos hpr] at hs
        cases hp : d.ptpool n i with
        | PDEID => rw [hp] at hs; cases hs
        | PDEUnPresent => rw [hp] at hs; cases hs
        | PDEUndef => rw [hp] at hs; cases hs
        | PDEValid pi pdt =>
          rw [hp] at hs; simp only [Option.some.injEq] at hs
          obtain ⟨σ', l', hr, hc', hlk'⟩ := pteStore_run εR hL hcs hlk hM.pt hnp hi1 hv1 hn hi hva hp
            (.bin .add (.bin .mul (.var "padr") (.const 4096)) (.var "perm"))
            (w := BitVec.ofNat 32 padr * 4096 + BitVec.ofNat 32 perm) (fun τ hτ => by
              show τ "padr" * 4096 + τ "perm" = _
              rw [hτ _ (by decide), hτ _ (by decide), hpa, hpe])
          have hrel : RelPTE (.PTEValid padr p) (BitVec.ofNat 32 padr * 4096 + BitVec.ofNat 32 perm) := by
            show (BitVec.ofNat 32 padr * 4096 + BitVec.ofNat 32 perm).toNat = padr * 4096 + PermtoZ p
            have e := PermZ_eq hz
            have := perm_le p
            rw [← e]
            simp [BitVec.toNat_add, BitVec.toNat_mul]; omega
          have hpt := pte_update hL hM.pt hnp hi1 hp hv1 (.PTEValid padr p) _ hrel
          rw [hs] at hpt
          exact ⟨σ', l', _, d1, hr, hc', ⟨mm_frame (d' := d1.toRData) hL hM.mm (by rw [← hs]) (by rw [← hs])
            (by rw [← hs]) (fun k hk => sc_ne _ _ (by omega)), hpt⟩, hlk',
            fun k hk => sc_ne _ _ (by omega), hs0⟩
      · rw [if_neg hpr] at hs; cases hs

/-- **`rmv_PTE` refines `rmvPTE_spec`.** -/
theorem rmvPTE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (n i vadr : Nat) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "i" = BitVec.ofNat 32 i ∧
        σ "vadr" = BitVec.ofNat 32 vadr ∧ ∃ d1, rmvPTE_spec num_proc n i vadr d = some d1)
      (rmvPTES pb fb)
      (fun _ d _ d' => rmvPTE_spec num_proc n i vadr d = some d') := by
  intro σ l b d hlk hcs hM ⟨hn, hi, hva, d1, hs⟩
  have := hL.hib; have := hL.hfb; have := hL.hend; have := hL.hpb
  have hs0 := hs
  unfold rmvPTE_spec at hs
  have hc : d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr := by
    by_cases h : d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n i vadr
    · exact h
    · rw [if_neg h] at hs; cases hs
  rw [if_pos hc] at hs
  obtain ⟨-, -, ⟨hnp, hi1⟩, hv1⟩ := hc
  by_cases hPT : n = d.PT
  · rw [if_pos hPT] at hs; cases hs
  · rw [if_neg hPT] at hs
    cases hp : d.ptpool n i with
    | PDEID => rw [hp] at hs; cases hs
    | PDEUnPresent => rw [hp] at hs; cases hs
    | PDEUndef => rw [hp] at hs; cases hs
    | PDEValid pi pdt =>
      rw [hp] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨σ', l', hr, hc', hlk'⟩ := pteStore_run εR hL hcs hlk hM.pt hnp hi1 hv1 hn hi hva hp
        (.const 0) (w := 0) (fun _ _ => rfl)
      have hpt := pte_update hL hM.pt hnp hi1 hp hv1 .PTEUnPresent 0 rfl
      rw [hs] at hpt
      exact ⟨σ', l', _, d1, hr, hc', ⟨mm_frame (d' := d1.toRData) hL hM.mm (by rw [← hs]) (by rw [← hs])
        (by rw [← hs]) (fun k hk => sc_ne _ _ (by omega)), hpt⟩, hlk',
        fun k hk => sc_ne _ _ (by omega), hs0⟩

end Write

end MPTIntro
