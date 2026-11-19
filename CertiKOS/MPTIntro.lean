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
* `setPT'_spec` is not ported yet. It needs `PMap_valid` and `PMap_kern`.

This file has the state, the specifications and the relation to memory. The
C code and its proofs come next.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace MPTIntro

open LockRegion (Region)
open ClightL
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

end MPTIntro
