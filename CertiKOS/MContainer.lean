import CertiKOS.MALOp
import CertiKOS.KernContainer

/-!
# mCertiKOS containers, ported

The container primitives of mCertiKOS (the layer interface `MContainer`,
implemented by the C code in `mcertikos/mm/MALTCSource.v`). This file follows
the sources. `KernContainer.lean` was a prototype with its own specification.

Ported from `layerlib/AuxStateDataType.v`: `Container`, `ContainerPool`.

Ported from `objects/ObjContainer.v`: `container_get_parent_spec`,
`container_get_nchildren_spec`, `container_get_quota_spec`,
`container_get_usage_spec`, `container_can_consume_spec`,
`container_split_spec`, `container_alloc_spec`.

Ported from `mm/MALTCSource.v`: the C code of those primitives.

Ported from `mm/ContainerGen.v`: `match_container`, the relation between a
container and its five words (quota, usage, parent, nchildren, used).

mCertiKOS has no `container_free`. Its specification is commented out in the
sources, so there is none here.

What differs from the sources: as in `MALOp.lean` (no `ikern`/`ihost`, `Nat`
for `Z`, a lock region for memory). The container table has its own lock, and
`container_alloc` calls `palloc` under the allocation table's lock. In the
sequential sources `container_alloc_spec` changes both tables in one step.
Here the allocation table `a` that `palloc` works on is the one it finds
when it takes that lock.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace MContainer

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernFrame
open KernPAlloc (ofNat_ne)
open KernContainer (nest nest_run cell cellE rd_cell wr_cell)
open MALOp

/-! ## Abstract data (`AuxStateDataType.v`) -/

structure Container where
  cquota : Nat
  cusage : Nat
  cparent : Nat
  cchildren : List Nat
  cused : Bool

abbrev ContainerPool := Nat → Container

/-- `RData` with the container pool `AC`. -/
structure RData extends PData where
  AC : ContainerPool

/-! ## Specifications (`ObjContainer.v`) -/

section Specs
variable (num_id max_children : Nat)

def container_get_parent_spec (i : Nat) (d : RData) : Option Nat :=
  if (d.AC i).cused = true then some (d.AC i).cparent else none

def container_get_nchildren_spec (i : Nat) (d : RData) : Option Nat :=
  if (d.AC i).cused = true then some (d.AC i).cchildren.length else none

def container_get_quota_spec (i : Nat) (d : RData) : Option Nat :=
  if (d.AC i).cused = true then some (d.AC i).cquota else none

def container_get_usage_spec (i : Nat) (d : RData) : Option Nat :=
  if (d.AC i).cused = true then some (d.AC i).cusage else none

/-- Whether container `i` can use `n` more pages: `0 ≤ n ≤ quota - usage`. -/
def container_can_consume_spec (i n : Nat) (d : RData) : Option Nat :=
  if (d.AC i).cused = true then
    some (if n + (d.AC i).cusage ≤ (d.AC i).cquota then 1 else 0)
  else none

/-- **`container_split_spec`**: give `q` of container `id`'s quota to a new child. -/
def container_split_spec (id q : Nat) (d : RData) : Option (RData × Nat) :=
  let c := d.AC id
  let i := id * max_children + 1 + c.cchildren.length
  if c.cused = true ∧ i < num_id ∧ c.cchildren.length < max_children ∧ q + c.cusage ≤ c.cquota then
    let AC1 := setAt d.AC id ⟨c.cquota, c.cusage + q, c.cparent, i :: c.cchildren, c.cused⟩
    some ({ d with AC := setAt AC1 i ⟨q, 0, id, [], true⟩ }, i)
  else none

/-- **`container_alloc_spec`**: charge container `id` one page and allocate it.
Returns 0 when the container is at its quota. -/
def container_alloc_spec (id : Nat) (d : RData) : Option (RData × Nat) :=
  let c := d.AC id
  if d.init = true ∧ c.cused = true then
    if c.cusage < c.cquota then
      match first_free d.AT d.nps with
      | some i =>
        some ({ d with AT := setAt d.AT i (.ATValid true .ATNorm 0), pperm := setAt d.pperm i .PGAlloc,
                       AC := setAt d.AC id ⟨c.cquota, c.cusage + 1, c.cparent, c.cchildren, c.cused⟩ }, i)
      | none => none
    else some (d, 0)
  else none

end Specs

/-! ## The container table in a region (`ContainerGen.v`) -/

/-- `match_container`: quota, usage, parent, nchildren, used. -/
def MatchCont (c : Container) (v1 v2 v3 v4 v5 : Val) : Prop :=
  if c.cused = true then
    v1.toNat = c.cquota ∧ v2.toNat = c.cusage ∧ v3.toNat = c.cparent ∧ v4.toNat = c.cchildren.length ∧ v5 = 1
  else v5 = 0

def MatchC (num_id : Nat) (AC : ContainerPool) (b : Region) : Prop :=
  ∀ i, i < num_id →
    MatchCont (AC i) (b (5 * i)) (b (5 * i + 1)) (b (5 * i + 2)) (b (5 * i + 3)) (b (5 * i + 4))

section Cell
variable {num_id : Nat} (hnum : 5 * num_id < 2 ^ 32)
include hnum

theorem cell0 {i : Nat} (hi : i < num_id) : cell (BitVec.ofNat 32 i) 0 = 5 * i := by
  simp [cell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell1 {i : Nat} (hi : i < num_id) : cell (BitVec.ofNat 32 i) 1 = 5 * i + 1 := by
  simp [cell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell2 {i : Nat} (hi : i < num_id) : cell (BitVec.ofNat 32 i) 2 = 5 * i + 2 := by
  simp [cell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell3 {i : Nat} (hi : i < num_id) : cell (BitVec.ofNat 32 i) 3 = 5 * i + 3 := by
  simp [cell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell4 {i : Nat} (hi : i < num_id) : cell (BitVec.ofNat 32 i) 4 = 5 * i + 4 := by
  simp [cell, BitVec.toNat_add, BitVec.toNat_mul]; omega

end Cell

theorem MatchC.used {num_id : Nat} {AC : ContainerPool} {b : Region} (h : MatchC num_id AC b) {i : Nat}
    (hi : i < num_id) (hu : (AC i).cused = true) :
    (b (5 * i)).toNat = (AC i).cquota ∧ (b (5 * i + 1)).toNat = (AC i).cusage ∧
    (b (5 * i + 2)).toNat = (AC i).cparent ∧ (b (5 * i + 3)).toNat = (AC i).cchildren.length ∧
    b (5 * i + 4) = 1 := by
  have := h i hi; unfold MatchCont at this; rw [if_pos hu] at this; exact this

/-! ## The getters refine their specifications -/

section Getters
variable {num_id : Nat} (hnum : 5 * num_id < 2 ^ 32)
include hnum

theorem get_quota_ref {d : RData} {b : Region} (hM : MatchC num_id d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_quota_spec i d = some v) : b (cell (BitVec.ofNat 32 i) 0) = BitVec.ofNat 32 v := by
  unfold container_get_quota_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell0 hnum hi]; exact val_of_toNat (hM.used hi hu).1 (by rw [← (hM.used hi hu).1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

theorem get_usage_ref {d : RData} {b : Region} (hM : MatchC num_id d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_usage_spec i d = some v) : b (cell (BitVec.ofNat 32 i) 1) = BitVec.ofNat 32 v := by
  unfold container_get_usage_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell1 hnum hi]; exact val_of_toNat (hM.used hi hu).2.1 (by rw [← (hM.used hi hu).2.1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

theorem get_parent_ref {d : RData} {b : Region} (hM : MatchC num_id d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_parent_spec i d = some v) : b (cell (BitVec.ofNat 32 i) 2) = BitVec.ofNat 32 v := by
  unfold container_get_parent_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell2 hnum hi]
    exact val_of_toNat (hM.used hi hu).2.2.1 (by rw [← (hM.used hi hu).2.2.1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

theorem get_nchildren_ref {d : RData} {b : Region} (hM : MatchC num_id d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_nchildren_spec i d = some v) : b (cell (BitVec.ofNat 32 i) 3) = BitVec.ofNat 32 v := by
  unfold container_get_nchildren_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell3 hnum hi]
    exact val_of_toNat (hM.used hi hu).2.2.2.1 (by rw [← (hM.used hi hu).2.2.2.1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

end Getters

/-! ## `container_alloc` -/

/-- What `container_alloc(id)` does: to the container table `b`, to the
allocation table `a` that `palloc` finds, and what it returns.
`u = usage; q = quota; if (u == q) return 0; usage = u + 1; return palloc();` -/
def ctAllocC (maxpage : Nat) (b a : Region) (id : Val) : Region × Region × Val :=
  if b (cell id 1) = b (cell id 0) then (b, a, 0)
  else (setCell b (cell id 1) (b (cell id 1) + 1), (pallocC maxpage a).1, (pallocC maxpage a).2)

/-- **`container_alloc` refines `container_alloc_spec`.** `cvalid_usage` (usage
is at most quota) is the part of `Container_valid` it needs: the C code tests
`u == q` where the specification tests `usage < quota`. -/
theorem alloc_ref {maxpage num_id : Nat} (hmax : 3 * maxpage < 2 ^ 32) (hnum : 5 * num_id < 2 ^ 32)
    {kl kh : Nat} {d d' : RData} {b a : Region} {id r : Nat} (hC : MatchC num_id d.AC b)
    (hA : MatchD maxpage d.toPData a) (hI : ATInv maxpage kl kh d.toPData) (hid : id < num_id)
    (hu : (d.AC id).cusage ≤ (d.AC id).cquota) (h : container_alloc_spec id d = some (d', r)) :
    MatchC num_id d'.AC (ctAllocC maxpage b a (BitVec.ofNat 32 id)).1 ∧
    MatchD maxpage d'.toPData (ctAllocC maxpage b a (BitVec.ofNat 32 id)).2.1 ∧
    (ctAllocC maxpage b a (BitVec.ofNat 32 id)).2.2 = BitVec.ofNat 32 r := by
  unfold container_alloc_spec at h
  simp only at h
  by_cases hiu : d.init = true ∧ (d.AC id).cused = true
  · rw [if_pos hiu] at h
    obtain ⟨hinit, hused⟩ := hiu
    obtain ⟨hq, hus, hpa, hnc, hud⟩ := hC.used hid hused
    unfold ctAllocC
    rw [cell1 hnum hid, cell0 hnum hid]
    by_cases hlt : (d.AC id).cusage < (d.AC id).cquota
    · rw [if_pos hlt] at h
      have hne : ¬ b (5 * id + 1) = b (5 * id) := fun e => by
        have := congrArg BitVec.toNat e; omega
      rw [if_neg hne]
      cases hff : first_free d.AT d.nps with
      | none => rw [hff] at h; cases h
      | some i =>
        rw [hff] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        have hp : palloc'_spec d.toPData = some ({ d.toPData with
            AT := setAt d.AT i (.ATValid true .ATNorm 0), pperm := setAt d.pperm i .PGAlloc }, i) := by
          simp [palloc'_spec, hinit, hff]
        obtain ⟨g1, g2⟩ := palloc_ref hmax hA hI hp
        refine ⟨fun j hj => ?_, g1, g2⟩
        by_cases hji : j = id
        · subst hji
          simp only [setAt_eq, setCell, show ¬ (5 * j = 5 * j + 1) by omega,
            show ¬ (5 * j + 2 = 5 * j + 1) by omega, show ¬ (5 * j + 3 = 5 * j + 1) by omega,
            show ¬ (5 * j + 4 = 5 * j + 1) by omega, if_true, if_false]
          unfold MatchCont
          rw [if_pos hused]
          refine ⟨hq, ?_, hpa, hnc, hud⟩
          have hb := (b (5 * j)).isLt
          simp only [BitVec.toNat_add]; simp; omega
        · simp only [setAt_ne _ _ hji, setCell, show ¬ (5 * j = 5 * id + 1) by omega,
            show ¬ (5 * j + 1 = 5 * id + 1) by omega, show ¬ (5 * j + 2 = 5 * id + 1) by omega,
            show ¬ (5 * j + 3 = 5 * id + 1) by omega, show ¬ (5 * j + 4 = 5 * id + 1) by omega, if_false]
          exact hC j hj
    · rw [if_neg hlt] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have he : b (5 * id + 1) = b (5 * id) := BitVec.eq_of_toNat_eq (by omega)
      rw [if_pos he]
      exact ⟨hC, hA, rfl⟩
  · rw [if_neg hiu] at h; cases h

end MContainer
