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

/-! ## The C code of `container_alloc` (`MALTCSource.v`) -/

/-- `u = CT[id].usage; q = CT[id].quota; if (u == q) return 0; CT[id].usage = u + 1; return palloc();` -/
def ctAllocCS (atv : Val) (maxpage : Nat) : Stmt APrim :=
  .seq (.call "u" .pull [lkE, cellE "id" 1]) (.seq (.call "q" .pull [lkE, cellE "id" 0])
    (.ite (.bin .eq (.var "u") (.var "q")) (.assign "r" (.const 0))
      (.seq (.call "_" .push [lkE, cellE "id" 1, .bin .add (.var "u") (.const 1)])
        (nest atv (palloc maxpage)))))

/-- `container_alloc(id)` under the container table's lock. The result is in `r`. -/
def container_alloc (atv : Val) (maxpage : Nat) : Stmt APrim :=
  .seq acquireA (.seq (ctAllocCS atv maxpage) relA)

theorem palloc_lk (maxpage : Nat) : LkS (palloc maxpage) := by
  simp [LkS, palloc, acquireA, loopA, pallocCS, getNpsS, pallocLoop, loopBody, isNormS, atGetS, atSetS,
    atSetCS, relA]

theorem palloc_fr (maxpage : Nat) (z : Ident) (h1 : z ≠ "t") (h2 : z ≠ "n") (h3 : z ≠ "_") (h4 : z ≠ "v")
    (h5 : z ≠ "tnps") (h6 : z ≠ "pi") (h7 : z ≠ "fi") (h8 : z ≠ "isn") (h9 : z ≠ "cur") (h10 : z ≠ "r") :
    frS z (palloc maxpage) = true := by
  simp [frS, palloc, acquireA, loopA, pallocCS, getNpsS, pallocLoop, loopBody, isNormS, atGetS, atSetS,
    atSetCS, relA, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7,
    Ne.symm h8, Ne.symm h9, Ne.symm h10]

/-- **The body of `container_alloc` computes `ctAllocC`.** `a` is the
allocation table `palloc` found when it took its lock. -/
theorem ctAllocCS_run {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    {atv : Val} (hF : ∀ tn, LockArray.FairA ε c atv.toNat tn bound) {maxpage : Nat}
    (hmax : 3 * maxpage < 2 ^ 32) {i : Nat} (hi : i ≠ atv.toNat) (σ : Locals) (l : RLog) (b : Region)
    (hlk : (σ "lk").toNat = i) (hcs : CSt c i atv.toNat l b) :
    ∃ σ' l' a, Runs (rprimsA εR c) (ctAllocCS atv maxpage) σ l σ' l' ∧
      CSt c i atv.toNat l' (ctAllocC maxpage b a (σ "id")).1 ∧ σ' "lk" = σ "lk" ∧
      σ' "r" = (ctAllocC maxpage b a (σ "id")).2.2 := by
  let U := b (cell (σ "id") 1)
  let Q := b (cell (σ "id") 0)
  let σ0 := σ.set "u" U
  let σ1 := σ0.set "q" Q
  have hr0 : Runs (rprimsA εR c) (.call "u" .pull [lkE, cellE "id" 1]) σ l σ0 l := rd_cell hcs hlk "u" "id" 1 rfl
  have hr1 : Runs (rprimsA εR c) (.call "q" .pull [lkE, cellE "id" 0]) σ0 l σ1 l :=
    rd_cell hcs (σ := σ0) (by simp [σ0, Locals.set, hlk]) "q" "id" 0 (by simp [σ0, Locals.set])
  have hlk1 : σ1 "lk" = σ "lk" := by simp [σ1, σ0, Locals.set]
  have hu1 : σ1 "u" = U := by simp [σ1, σ0, Locals.set]
  have hq1 : σ1 "q" = Q := by simp [σ1, σ0, Locals.set]
  have hid1 : σ1 "id" = σ "id" := by simp [σ1, σ0, Locals.set]
  have hgd : (Expr.bin .eq (.var "u") (.var "q")).eval σ1 = if σ1 "u" = σ1 "q" then 1 else 0 := rfl
  by_cases he : U = Q
  · have hsp : ∀ a, ctAllocC maxpage b a (σ "id") = (b, a, 0) := fun a => if_pos he
    refine ⟨σ1.set "r" 0, l, fun _ => 0, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_true
      (by rw [hgd, hu1, hq1, if_pos he]; decide) (Runs.assign _ _))), ?_, ?_, ?_⟩
    · rw [hsp]; exact hcs
    · rw [Locals.set_other _ _ (by decide)]; exact hlk1
    · rw [hsp]; simp
  · obtain ⟨l2, hw, hc2⟩ := wr_cell (εR := εR) hcs (σ := σ1) (by rw [hlk1]; exact hlk) "id" 1
      (.bin .add (.var "u") (.const 1)) hid1
    have hev : (Expr.bin .add (.var "u") (.const 1)).eval σ1 = U + 1 := by
      simp only [Expr.eval, BinOp.eval]; rw [hu1]
    rw [hev] at hc2
    let σ2 := σ1.set "_" 0
    have hlk2 : σ2 "lk" = σ "lk" := by simp [σ2, Locals.set, hlk1]
    obtain ⟨S, H, hl, hh, hid, hb⟩ := hc2
    obtain ⟨σp, rb, S3, H1, H3, hrun, hl3, hid3, -, hr⟩ :=
      palloc_guarantee hE hRR hc hRA hl (iv := atv) hid bound K hK (hF _)
        ((σ2.set "plk" (σ2 "lk")).set "lk" atv) (by simp) hmax
    obtain ⟨hnest, hc3⟩ := nest_run (palloc_lk _)
      (palloc_fr _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      (palloc_fr _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
      hi hl hh hb hrun hl3 hid3
    have hsp : ctAllocC maxpage b (hmemR atv.toNat H1) (σ "id") =
        (setCell b (cell (σ "id") 1) (U + 1), (pallocC maxpage (hmemR atv.toNat H1)).1,
          (pallocC maxpage (hmemR atv.toNat H1)).2) := if_neg he
    refine ⟨σp.set "lk" (σ2 "lk"), rb, hmemR atv.toNat H1, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_false
      (by rw [hgd, hu1, hq1, if_neg he]) (Runs.seq hw hnest))), ?_, ?_, ?_⟩
    · rw [hsp]; exact hc3
    · simp [hlk2]
    · rw [hsp, Locals.set_other _ _ (by decide)]; exact hr

/-- **`container_alloc(id)` computes `ctAllocC`** of the container table the
previous holder released. -/
theorem container_alloc_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {atv : Val} (hi : iv.toNat ≠ atv.toNat) (hidat : (S.lk atv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hFat : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    (σ : Locals) (hσ : σ "lk" = iv) {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR) (a : Region),
      Star (rprimsA εR c) ⟨container_alloc atv maxpage, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk atv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (ctAllocC maxpage (hmemR iv.toNat H1) a (σ "id")).1 ∧
      σ' "r" = (ctAllocC maxpage (hmemR iv.toNat H1) a (σ "id")).2.2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hidj, hfr, a, hR1, hR2⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle (j := atv.toNat) (fun h => hi h.symm) hidat bound K hK hF σ hσ
      (ctAllocCS atv maxpage)
      (fun b σ b' σ' => ∃ a, b' = (ctAllocC maxpage b a (σ "id")).1 ∧
        σ' "r" = (ctAllocC maxpage b a (σ "id")).2.2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', a, hr, hc', hlk', hres⟩ := ctAllocCS_run hE hRR hc hRA bound K hK hFat hmax
          hi σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, a, rfl, hres⟩)
  have hd := hfr "id" (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, a, hrun, hl3, hid, hidj, ?_, ?_⟩
  · rw [hR1, hd]
  · rw [Locals.set_other _ _ (by decide), hR2, hd]

/-- **`container_alloc(id)` refines `container_alloc_spec`.** Suppose the
container table the previous holder released matches `d.AC`, the allocation
table `a` that `palloc` found matches `d`'s, the invariants hold, and the
specification is defined. Then the container table released matches the
specification's result, so does the allocation table `palloc` left, and `r`
is the page. -/
theorem container_alloc_refines {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {atv : Val} (hi : iv.toNat ≠ atv.toNat) (hidat : (S.lk atv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hFat : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    (σ : Locals) (hσ : σ "lk" = iv) {maxpage num_id : Nat} (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : 5 * num_id < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR) (a a' : Region),
      Star (rprimsA εR c) ⟨container_alloc atv maxpage, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk atv.toNat).phase c = .idle ∧
      ∀ (kl kh : Nat) (d d' : RData) (id r : Nat), σ "id" = BitVec.ofNat 32 id → id < num_id →
        MatchC num_id d.AC (hmemR iv.toNat H1) → MatchD maxpage d.toPData a →
        ATInv maxpage kl kh d.toPData → (d.AC id).cusage ≤ (d.AC id).cquota →
        container_alloc_spec id d = some (d', r) →
        MatchC num_id d'.AC (hmemR iv.toNat H3) ∧ MatchD maxpage d'.toPData a' ∧
          σ' "r" = BitVec.ofNat 32 r := by
  obtain ⟨σ', rb, S3, H1, H3, a, hrun, hl3, hid, hidj, hm, hr⟩ :=
    container_alloc_guarantee hE hRR hc hRA hl hidle hi hidat bound K hK hF hFat σ hσ hmax
  refine ⟨σ', rb, S3, H1, H3, a, (ctAllocC maxpage (hmemR iv.toNat H1) a (σ "id")).2.1, hrun, hl3, hid, hidj,
    fun kl kh d d' id r hsid hlt hC hA hI hu hs => ?_⟩
  obtain ⟨g1, g2, g3⟩ := alloc_ref hmax hnum hC hA hI hlt hu hs
  rw [hm, hr, hsid]; exact ⟨g1, g2, g3⟩

/-! ## The getters (`MALTCSource.v`) -/

/-- `return container_LOC[id].field;` for field `f`: 0 quota, 1 usage, 2 parent, 3 nchildren. -/
def getterCS (f : Val) : Stmt APrim := .call "r" .pull [lkE, cellE "id" f]

def getter (f : Val) : Stmt APrim := .seq acquireA (.seq (getterCS f) relA)

/-- **A getter returns the field** of the table the previous holder released,
and releases the table unchanged. With `get_quota_ref`, `get_usage_ref`,
`get_parent_ref` and `get_nchildren_ref` this is refinement of
`container_get_quota_spec` and the other three. -/
theorem getter_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (f : Val) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨getter f, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = hmemR iv.toNat H1 ∧ σ' "r" = hmemR iv.toNat H1 (cell (σ "id") f) := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hfr, hR1, hR2⟩ :=
    cs_guarantee1 hE hRR hc hRA hl hidle bound K hK hF σ hσ (getterCS f)
      (fun b σ b' σ' => b' = b ∧ σ' "r" = b (cell (σ "id") f))
      (fun σ l b hlk hcs => ⟨σ.set "r" (b (cell (σ "id") f)), l, b,
        cs1_rd hcs (by rw [hlk]) "r" (cellE "id" f), hcs,
        by rw [Locals.set_other _ _ (by decide)]; exact hlk, rfl, by simp⟩)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hR1, ?_⟩
  rw [Locals.set_other _ _ (by decide), hR2, hfr "id" (by decide) (by decide) (by decide) (by decide)]

/-! ## `container_split` -/

/-- The child slot: `id * MAX_CHILDREN + 1 + nc`. -/
def childC (mc : Val) (b : Region) (id : Val) : Val := id * mc + 1 + b (cell id 3)

/-- What `container_split(id, q)` does to the table, and the child it returns. -/
def ctSplitC (mc : Val) (b : Region) (id q : Val) : Region × Val :=
  let ch := childC mc b id
  let b5 := setCell (setCell (setCell (setCell (setCell b (cell ch 4) 1) (cell ch 0) q) (cell ch 1) 0)
    (cell ch 2) id) (cell ch 3) 0
  (setCell (setCell b5 (cell id 1) (b5 (cell id 1) + q)) (cell id 3) (b (cell id 3) + 1), ch)

/-- ```
nc = CT[id].nchildren; ch = id * MAX_CHILDREN + 1 + nc;
CT[ch].used = 1; CT[ch].quota = quota; CT[ch].usage = 0; CT[ch].parent = id; CT[ch].nchildren = 0;
CT[id].usage += quota; CT[id].nchildren = nc + 1; return ch;
``` -/
def ctSplitCS (mcv : Val) : Stmt APrim :=
  .seq (.call "nc" .pull [lkE, cellE "id" 3])
  (.seq (.assign "ch" (.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv)) (.const 1)) (.var "nc")))
  (.seq (.call "_" .push [lkE, cellE "ch" 4, .const 1])
  (.seq (.call "_" .push [lkE, cellE "ch" 0, .var "amt"])
  (.seq (.call "_" .push [lkE, cellE "ch" 1, .const 0])
  (.seq (.call "_" .push [lkE, cellE "ch" 2, .var "id"])
  (.seq (.call "_" .push [lkE, cellE "ch" 3, .const 0])
  (.seq (.call "u" .pull [lkE, cellE "id" 1])
  (.seq (.call "_" .push [lkE, cellE "id" 1, .bin .add (.var "u") (.var "amt")])
  (.seq (.call "_" .push [lkE, cellE "id" 3, .bin .add (.var "nc") (.const 1)])
    (.assign "r" (.var "ch")))))))))))

def container_split (mcv : Val) : Stmt APrim := .seq acquireA (.seq (ctSplitCS mcv) relA)

theorem wr1 {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (y : Ident) (f : Val) (ve : Expr) {id v : Val} (hy : σ y = id)
    (hv : ve.eval σ = v) :
    ∃ l', Runs (rprimsA εR c) (.call "_" .push [lkE, cellE y f, ve]) σ l (σ.set "_" 0) l' ∧
      CS1 c i l' (setCell b (cell id f) v) := by
  subst hy hv; exact cs1_wr h hlk (cellE y f) ve

theorem set_self {σ : Locals} {x : Ident} {v : Val} (h : σ x = v) : σ.set x v = σ := by
  funext y; by_cases e : y = x
  · subst e; simp [h]
  · simp [Locals.set, e]

/-- **The body of `container_split` computes `ctSplitC`.** -/
theorem ctSplitCS_run (εR : REnv) {c : CPU} {i : Nat} (mcv : Val) (σ : Locals) (l : RLog) (b : Region)
    (hlk : (σ "lk").toNat = i) (hcs : CS1 c i l b) :
    ∃ σ' l', Runs (rprimsA εR c) (ctSplitCS mcv) σ l σ' l' ∧
      CS1 c i l' (ctSplitC mcv b (σ "id") (σ "amt")).1 ∧ σ' "lk" = σ "lk" ∧
      σ' "r" = (ctSplitC mcv b (σ "id") (σ "amt")).2 := by
  let ID := σ "id"
  let Q := σ "amt"
  let NC := b (cell ID 3)
  let CH := childC mcv b ID
  let σ0 := σ.set "nc" NC
  let σ1 := σ0.set "ch" CH
  let σ2 := σ1.set "_" 0
  have h0 : Runs (rprimsA εR c) (.call "nc" .pull [lkE, cellE "id" 3]) σ l σ0 l :=
    cs1_rd hcs hlk "nc" (cellE "id" 3)
  have h1 : Runs (rprimsA εR c) (.assign "ch" (.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv))
      (.const 1)) (.var "nc"))) σ0 l σ1 l := by
    have h := Runs.assign (P := rprimsA εR c) (σ := σ0) (l := l) "ch"
      (.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv)) (.const 1)) (.var "nc"))
    have e : (Expr.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv)) (.const 1)) (.var "nc")).eval σ0
        = CH := by simp [Expr.eval, BinOp.eval, σ0, Locals.set, CH, childC, NC, ID]
    rw [e] at h; exact h
  have hlk1 : (σ1 "lk").toNat = i := by simpa [σ1, σ0, Locals.set] using hlk
  have hlk2 : (σ2 "lk").toNat = i := by simpa [σ2, σ1, σ0, Locals.set] using hlk
  have hch1 : σ1 "ch" = CH := by simp [σ1]
  have hch2 : σ2 "ch" = CH := by simp [σ2, σ1, Locals.set]
  have hid2 : σ2 "id" = ID := by simp [σ2, σ1, σ0, Locals.set, ID]
  have hs2 : σ2.set "_" 0 = σ2 := set_self (by simp [σ2])
  obtain ⟨l1, w1, c1⟩ := wr1 (εR := εR) hcs hlk1 "ch" 4 (.const 1) hch1 (v := 1) rfl
  obtain ⟨l2, w2, c2⟩ := wr1 (εR := εR) c1 hlk2 "ch" 0 (.var "amt") hch2 (v := Q)
    (by show σ2 "amt" = Q; simp [σ2, σ1, σ0, Locals.set, Q])
  rw [hs2] at w2
  obtain ⟨l3, w3, c3⟩ := wr1 (εR := εR) c2 hlk2 "ch" 1 (.const 0) hch2 (v := 0) rfl
  rw [hs2] at w3
  obtain ⟨l4, w4, c4⟩ := wr1 (εR := εR) c3 hlk2 "ch" 2 (.var "id") hch2 (v := ID) hid2
  rw [hs2] at w4
  obtain ⟨l5, w5, c5⟩ := wr1 (εR := εR) c4 hlk2 "ch" 3 (.const 0) hch2 (v := 0) rfl
  rw [hs2] at w5
  let B5 := setCell (setCell (setCell (setCell (setCell b (cell CH 4) 1) (cell CH 0) Q) (cell CH 1) 0)
    (cell CH 2) ID) (cell CH 3) 0
  let σ3 := σ2.set "u" (B5 (cell ID 1))
  have h6 : Runs (rprimsA εR c) (.call "u" .pull [lkE, cellE "id" 1]) σ2 l5 σ3 l5 := by
    have h := cs1_rd (εR := εR) c5 hlk2 "u" (cellE "id" 1)
    have e : ((cellE "id" 1).eval σ2).toNat = cell ID 1 := by show cell (σ2 "id") 1 = _; rw [hid2]
    rw [e] at h; exact h
  have hlk3 : (σ3 "lk").toNat = i := by simpa [σ3, Locals.set] using hlk2
  have hid3 : σ3 "id" = ID := by simp [σ3, Locals.set, hid2]
  obtain ⟨l7, w7, c7⟩ := wr1 (εR := εR) c5 hlk3 "id" 1 (.bin .add (.var "u") (.var "amt")) hid3
    (v := B5 (cell ID 1) + Q) (by simp [Expr.eval, BinOp.eval, σ3, σ2, σ1, σ0, Locals.set, Q])
  let σ4 := σ3.set "_" 0
  have hlk4 : (σ4 "lk").toNat = i := by simpa [σ4, Locals.set] using hlk3
  have hid4 : σ4 "id" = ID := by simp [σ4, Locals.set, hid3]
  have hs4 : σ4.set "_" 0 = σ4 := set_self (by simp [σ4])
  obtain ⟨l8, w8, c8⟩ := wr1 (εR := εR) c7 hlk4 "id" 3 (.bin .add (.var "nc") (.const 1)) hid4
    (v := NC + 1) (by simp [Expr.eval, BinOp.eval, σ4, σ3, σ2, σ1, σ0, Locals.set])
  rw [hs4] at w8
  have h9 : Runs (rprimsA εR c) (.assign "r" (.var "ch")) σ4 l8 (σ4.set "r" CH) l8 := by
    have h := Runs.assign (P := rprimsA εR c) (σ := σ4) (l := l8) "r" (.var "ch")
    have e : (Expr.var "ch").eval σ4 = CH := by show σ4 "ch" = _; simp [σ4, σ3, Locals.set, hch2]
    rw [e] at h; exact h
  refine ⟨σ4.set "r" CH, l8, Runs.seq h0 (Runs.seq h1 (Runs.seq w1 (Runs.seq w2 (Runs.seq w3 (Runs.seq w4
    (Runs.seq w5 (Runs.seq h6 (Runs.seq w7 (Runs.seq w8 h9))))))))), c8, ?_, by simp [ctSplitC, CH, ID]⟩
  simp [σ4, σ3, σ2, σ1, σ0, Locals.set]

end MContainer
