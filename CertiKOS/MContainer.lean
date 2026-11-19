import CertiKOS.MALOp
import CertiKOS.Layer

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
for `Z`, a lock region for memory).

All memory-management state is in one region under one lock (`MatchMM`): the
allocation table at the bottom, the container table from cell `cb`. So a
primitive is one critical section, and `container_alloc_spec` changes both
tables in one step, as in the sources. The concurrent kernel (mC2) uses finer
locks. Its sources are not public, so that is not ported.

`container_alloc` is verified against `palloc`'s specification
(`palloc_triple`), not against its code. That is the layer discipline of
`Layer.lean`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace MContainer

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernFrame
open KernPAlloc (ofNat_ne)
open MALOp Layer

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

/-- Cell `f` of container `id`, in a table that starts at cell `cb`:
0 quota, 1 usage, 2 parent, 3 nchildren, 4 used. -/
def ccell (cb : Nat) (id f : Val) : Nat := (BitVec.ofNat 32 cb + id * 5 + f).toNat

/-- `cb + x * 5 + f` -/
def ccellE (cb : Nat) (x : Ident) (f : Val) : Expr :=
  .bin .add (.bin .add (.const (BitVec.ofNat 32 cb)) (.bin .mul (.var x) (.const 5))) (.const f)

/-- `match_container`: quota, usage, parent, nchildren, used. -/
def MatchCont (c : Container) (v1 v2 v3 v4 v5 : Val) : Prop :=
  if c.cused = true then
    v1.toNat = c.cquota ∧ v2.toNat = c.cusage ∧ v3.toNat = c.cparent ∧ v4.toNat = c.cchildren.length ∧ v5 = 1
  else v5 = 0

def MatchC (num_id cb : Nat) (AC : ContainerPool) (b : Region) : Prop :=
  ∀ i, i < num_id →
    MatchCont (AC i) (b (cb + 5 * i)) (b (cb + 5 * i + 1)) (b (cb + 5 * i + 2)) (b (cb + 5 * i + 3)) (b (cb + 5 * i + 4))

section Cell
variable {num_id cb : Nat} (hnum : cb + 5 * num_id < 2 ^ 32)
include hnum

theorem cell0 {i : Nat} (hi : i < num_id) : ccell cb (BitVec.ofNat 32 i) 0 = cb + 5 * i := by
  simp [ccell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell1 {i : Nat} (hi : i < num_id) : ccell cb (BitVec.ofNat 32 i) 1 = cb + 5 * i + 1 := by
  simp [ccell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell2 {i : Nat} (hi : i < num_id) : ccell cb (BitVec.ofNat 32 i) 2 = cb + 5 * i + 2 := by
  simp [ccell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell3 {i : Nat} (hi : i < num_id) : ccell cb (BitVec.ofNat 32 i) 3 = cb + 5 * i + 3 := by
  simp [ccell, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem cell4 {i : Nat} (hi : i < num_id) : ccell cb (BitVec.ofNat 32 i) 4 = cb + 5 * i + 4 := by
  simp [ccell, BitVec.toNat_add, BitVec.toNat_mul]; omega

end Cell

theorem MatchC.used {num_id cb : Nat} {AC : ContainerPool} {b : Region} (h : MatchC num_id cb AC b) {i : Nat}
    (hi : i < num_id) (hu : (AC i).cused = true) :
    (b (cb + 5 * i)).toNat = (AC i).cquota ∧ (b (cb + 5 * i + 1)).toNat = (AC i).cusage ∧
    (b (cb + 5 * i + 2)).toNat = (AC i).cparent ∧ (b (cb + 5 * i + 3)).toNat = (AC i).cchildren.length ∧
    b (cb + 5 * i + 4) = 1 := by
  have := h i hi; unfold MatchCont at this; rw [if_pos hu] at this; exact this

/-! ## The getters refine their specifications -/

section Getters
variable {num_id cb : Nat} (hnum : cb + 5 * num_id < 2 ^ 32)
include hnum

theorem get_quota_ref {d : RData} {b : Region} (hM : MatchC num_id cb d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_quota_spec i d = some v) : b (ccell cb (BitVec.ofNat 32 i) 0) = BitVec.ofNat 32 v := by
  unfold container_get_quota_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell0 hnum hi]; exact val_of_toNat (hM.used hi hu).1 (by rw [← (hM.used hi hu).1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

theorem get_usage_ref {d : RData} {b : Region} (hM : MatchC num_id cb d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_usage_spec i d = some v) : b (ccell cb (BitVec.ofNat 32 i) 1) = BitVec.ofNat 32 v := by
  unfold container_get_usage_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell1 hnum hi]; exact val_of_toNat (hM.used hi hu).2.1 (by rw [← (hM.used hi hu).2.1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

theorem get_parent_ref {d : RData} {b : Region} (hM : MatchC num_id cb d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_parent_spec i d = some v) : b (ccell cb (BitVec.ofNat 32 i) 2) = BitVec.ofNat 32 v := by
  unfold container_get_parent_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell2 hnum hi]
    exact val_of_toNat (hM.used hi hu).2.2.1 (by rw [← (hM.used hi hu).2.2.1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

theorem get_nchildren_ref {d : RData} {b : Region} (hM : MatchC num_id cb d.AC b) {i v : Nat} (hi : i < num_id)
    (h : container_get_nchildren_spec i d = some v) : b (ccell cb (BitVec.ofNat 32 i) 3) = BitVec.ofNat 32 v := by
  unfold container_get_nchildren_spec at h
  by_cases hu : (d.AC i).cused = true
  · rw [if_pos hu] at h; simp only [Option.some.injEq] at h; subst h
    rw [cell3 hnum hi]
    exact val_of_toNat (hM.used hi hu).2.2.2.1 (by rw [← (hM.used hi hu).2.2.2.1]; exact (b _).isLt)
  · rw [if_neg hu] at h; cases h

end Getters

/-! ## The memory-management region -/

/-- The allocation table and the container table share one region: the
allocation table at cells `0 .. 3 * maxpage`, the containers from cell `cb`. -/
structure MatchMM (maxpage num_id cb : Nat) (d : RData) (b : Region) : Prop where
  mAT : MatchD maxpage d.toPData b
  mAC : MatchC num_id cb d.AC b

/-- **`palloc`'s interface for the layers above**: it behaves as
`palloc'_spec`, leaves the containers alone, and assigns only its own
temporaries and `r`. Callers use this, not `palloc`'s code. -/
theorem palloc_triple (εR : REnv) (c : CPU) (i : Nat) {maxpage num_id cb kl kh : Nat}
    (hmax : 3 * maxpage < 2 ^ 32) (hcb : 3 * maxpage < cb) :
    Triple εR c i (MatchMM maxpage num_id cb) (fun k => k ≤ 3 * maxpage)
      (fun _ d => ATInv maxpage kl kh d.toPData ∧ d.init = true)
      (pallocCS maxpage)
      (fun σ d σ' d' => ∃ pd r, palloc'_spec d.toPData = some (pd, r) ∧ d' = ⟨pd, d.AC⟩ ∧
        σ' "r" = BitVec.ofNat 32 r ∧
        ∀ z, z ≠ "_" → z ≠ "tnps" → z ≠ "pi" → z ≠ "fi" → z ≠ "isn" → z ≠ "cur" → z ≠ "r" → σ' z = σ z) := by
  intro σ l b d hlk hcs hM ⟨hI, hin⟩
  obtain ⟨σ', l', hr, hc', hres⟩ := pallocCS_run εR hmax σ l b hlk hcs
  have hdef : ∃ pd r, palloc'_spec d.toPData = some (pd, r) := by
    unfold palloc'_spec; rw [if_pos hin]; cases first_free d.AT d.nps <;> exact ⟨_, _, rfl⟩
  obtain ⟨pd, r, hs⟩ := hdef
  obtain ⟨g1, g2⟩ := palloc_ref hmax hM.mAT hI hs
  have hn : (b (3 * maxpage)).toNat ≤ maxpage := by rw [← hM.mAT.mnps]; exact hI.valid_nps.2
  refine ⟨σ', l', (pallocC maxpage b).1, ⟨pd, d.AC⟩, hr, hc', ⟨g1, fun j hj => ?_⟩,
    hr.frame (pallocCS_fr maxpage), fun k hk => pallocC_frame hmax b hn (by omega), pd, r, hs, rfl,
    hres.trans g2,
    fun z h3 h5 h6 h7 h8 h9 h10 => hr.frame (pallocCS_frz maxpage z h3 h5 h6 h7 h8 h9 h10)⟩
  rw [pallocC_frame hmax b hn (show 3 * maxpage < cb + 5 * j by omega),
    pallocC_frame hmax b hn (show 3 * maxpage < cb + 5 * j + 1 by omega),
    pallocC_frame hmax b hn (show 3 * maxpage < cb + 5 * j + 2 by omega),
    pallocC_frame hmax b hn (show 3 * maxpage < cb + 5 * j + 3 by omega),
    pallocC_frame hmax b hn (show 3 * maxpage < cb + 5 * j + 4 by omega)]
  exact hM.mAC j hj

/-! ## `container_alloc` (`MALTCSource.v`) -/

/-- `u = CT[id].usage; q = CT[id].quota; if (u == q) return 0; CT[id].usage = u + 1; return palloc();` -/
def ctAllocCS (cb maxpage : Nat) : Stmt APrim :=
  .seq (.call "u" .pull [lkE, ccellE cb "id" 1]) (.seq (.call "q" .pull [lkE, ccellE cb "id" 0])
    (.ite (.bin .eq (.var "u") (.var "q")) (.assign "r" (.const 0))
      (.seq (.call "_" .push [lkE, ccellE cb "id" 1, .bin .add (.var "u") (.const 1)]) (pallocCS maxpage))))

/-- `container_alloc(id)` under the memory-management lock. The result is in `r`. -/
def container_alloc (cb maxpage : Nat) : Stmt APrim := .seq acquireA (.seq (ctAllocCS cb maxpage) relA)

/-- **`container_alloc` refines `container_alloc_spec`.** The proof calls
`palloc` through `palloc_triple`, its specification. `cvalid_usage` is needed
because the code tests `u == q` where the specification tests
`usage < quota`. -/
theorem container_alloc_triple (εR : REnv) (c : CPU) (i : Nat) {maxpage num_id cb kl kh : Nat}
    (hmax : 3 * maxpage < 2 ^ 32) (hcb : 3 * maxpage < cb) (hnum : cb + 5 * num_id < 2 ^ 32)
    (id : Nat) (hid : id < num_id) :
    Triple εR c i (MatchMM maxpage num_id cb) (fun k => k < cb + 5 * num_id)
      (fun σ d => σ "id" = BitVec.ofNat 32 id ∧ ATInv maxpage kl kh d.toPData ∧
        (d.AC id).cusage ≤ (d.AC id).cquota ∧ ∃ d1 r, container_alloc_spec id d = some (d1, r))
      (ctAllocCS cb maxpage)
      (fun _ d σ' d' => ∃ r, container_alloc_spec id d = some (d', r) ∧ σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hsid, hI, hu, d1, r, hs⟩
  have hs0 := hs
  unfold container_alloc_spec at hs
  simp only at hs
  have hiu : d.init = true ∧ (d.AC id).cused = true := by
    by_cases hn : d.init = true ∧ (d.AC id).cused = true
    · exact hn
    · rw [if_neg hn] at hs; cases hs
  rw [if_pos hiu] at hs
  obtain ⟨hinit, hused⟩ := hiu
  obtain ⟨hq, hus, hpa, hnc, hud⟩ := hM.mAC.used hid hused
  let σ0 := σ.set "u" (b (cb + 5 * id + 1))
  let σ1 := σ0.set "q" (b (cb + 5 * id))
  have hid0 : σ0 "id" = BitVec.ofNat 32 id := by simp [σ0, Locals.set, hsid]
  have hid1 : σ1 "id" = BitVec.ofNat 32 id := by simp [σ1, σ0, Locals.set, hsid]
  have hlk0 : (σ0 "lk").toNat = i := by simpa [σ0, Locals.set] using hlk
  have hlk1 : (σ1 "lk").toNat = i := by simpa [σ1, σ0, Locals.set] using hlk
  have hr0 : Runs (rprimsA εR c) (.call "u" .pull [lkE, ccellE cb "id" 1]) σ l σ0 l := by
    have h := cs1_rd (εR := εR) hcs hlk "u" (ccellE cb "id" 1)
    have e : ((ccellE cb "id" 1).eval σ).toNat = cb + 5 * id + 1 := by
      show ccell cb (σ "id") 1 = _; rw [hsid]; exact cell1 hnum hid
    rw [e] at h; exact h
  have hr1 : Runs (rprimsA εR c) (.call "q" .pull [lkE, ccellE cb "id" 0]) σ0 l σ1 l := by
    have h := cs1_rd (εR := εR) hcs hlk0 "q" (ccellE cb "id" 0)
    have e : ((ccellE cb "id" 0).eval σ0).toNat = cb + 5 * id := by
      show ccell cb (σ0 "id") 0 = _; rw [hid0]; exact cell0 hnum hid
    rw [e] at h; exact h
  have hgd : (Expr.bin .eq (.var "u") (.var "q")).eval σ1 = if σ1 "u" = σ1 "q" then 1 else 0 := rfl
  have hu1 : σ1 "u" = b (cb + 5 * id + 1) := by simp [σ1, σ0, Locals.set]
  have hq1 : σ1 "q" = b (cb + 5 * id) := by simp [σ1]
  by_cases hlt : (d.AC id).cusage < (d.AC id).cquota
  · rw [if_pos hlt] at hs
    cases hff : first_free d.AT d.nps with
    | none => rw [hff] at hs; cases hs
    | some p =>
      rw [hff] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      have hne : ¬ b (cb + 5 * id + 1) = b (cb + 5 * id) := fun e => by
        have := congrArg BitVec.toNat e; omega
      obtain ⟨l2, hw, hc2⟩ := cs1_wr (εR := εR) hcs hlk1 (ccellE cb "id" 1) (.bin .add (.var "u") (.const 1))
      have e1 : ((ccellE cb "id" 1).eval σ1).toNat = cb + 5 * id + 1 := by
        show ccell cb (σ1 "id") 1 = _; rw [hid1]; exact cell1 hnum hid
      have e2 : (Expr.bin .add (.var "u") (.const 1)).eval σ1 = b (cb + 5 * id + 1) + 1 := by
        simp only [Expr.eval, BinOp.eval]; rw [hu1]
      rw [e1, e2] at hc2
      -- the state between the write and the call
      have hlow : ∀ k, k ≤ 3 * maxpage →
          setCell b (cb + 5 * id + 1) (b (cb + 5 * id + 1) + 1) k = b k := fun k hk => by
        simp only [setCell]; rw [if_neg (by omega)]
      have hMmid : MatchMM maxpage num_id cb ⟨d.toPData, setAt d.AC id ⟨(d.AC id).cquota,
          (d.AC id).cusage + 1, (d.AC id).cparent, (d.AC id).cchildren, (d.AC id).cused⟩⟩
          (setCell b (cb + 5 * id + 1) (b (cb + 5 * id + 1) + 1)) := by
        refine ⟨⟨fun j hj => ?_, ?_⟩, fun j hj => ?_⟩
        · rw [hlow _ (by omega), hlow _ (by omega), hlow _ (by omega)]; exact hM.mAT.mat j hj
        · rw [hlow _ (Nat.le_refl _)]; exact hM.mAT.mnps
        · by_cases hji : j = id
          · rw [hji]
            simp only [setAt_eq]
            simp (disch := omega) only [setCell, if_pos, if_neg, ↓reduceIte]
            unfold MatchCont
            simp only
            rw [if_pos hused]
            refine ⟨hq, ?_, hpa, hnc, hud⟩
            have h1 : (1 : Val).toNat = 1 := rfl
            have hb := (b (cb + 5 * id)).isLt
            simp only [BitVec.toNat_add, h1]; omega
          · simp only [setAt_ne _ _ hji]
            simp (disch := omega) only [setCell, if_pos, if_neg, ↓reduceIte]
            exact hM.mAC j hj
      obtain ⟨σ', l', b', d', hrp, hc', hM', hlk', hfp, pd, r', hps, rfl, hr', -⟩ :=
        palloc_triple εR c i (kl := kl) (kh := kh) hmax hcb (σ1.set "_" 0) l2 _ _
          (by simpa [Locals.set] using hlk1) hc2 hMmid ⟨hI, hinit⟩
      have hpd : palloc'_spec d.toPData = some ({ d.toPData with
          AT := setAt d.AT p (.ATValid true .ATNorm 0), pperm := setAt d.pperm p .PGAlloc }, p) := by
        simp [palloc'_spec, hinit, hff]
      rw [hpd] at hps
      simp only [Option.some.injEq, Prod.mk.injEq] at hps; obtain ⟨rfl, rfl⟩ := hps
      refine ⟨σ', l', b', _, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_false
        (by rw [hgd, hu1, hq1, if_neg hne]) (Runs.seq hw hrp))), hc', hM', ?_, ?_, p, hs0, hr'⟩
      · rw [hlk']; simp [σ1, σ0, Locals.set]
      · intro k hk
        rw [hfp k (by omega)]; simp only [setCell]; rw [if_neg (by omega)]
  · rw [if_neg hlt] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    have he : b (cb + 5 * id + 1) = b (cb + 5 * id) := BitVec.eq_of_toNat_eq (by omega)
    refine ⟨σ1.set "r" 0, l, b, d, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_true
      (by rw [hgd, hu1, hq1, if_pos he]; decide) (Runs.assign _ _))), hcs, hM, ?_, fun _ _ => rfl, 0, hs0,
      by simp⟩
    simp [σ1, σ0, Locals.set]

/-- **`container_alloc(id)` under the lock refines `container_alloc_spec`.**
If the region found on acquiring matches `d`, the invariants hold and the
specification is defined, then the region released matches the
specification's result and `r` is the page. -/
theorem container_alloc_refines {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {maxpage num_id cb kl kh : Nat} (hmax : 3 * maxpage < 2 ^ 32)
    (hcb : 3 * maxpage < cb) (hnum : cb + 5 * num_id < 2 ^ 32) (id : Nat) (hid : id < num_id) :
    ∃ (σ1 : Locals) (r1 : RLog) (H1 : HLogR), Runs (rprimsA εR c) acquireA σ l σ1 r1 ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) ∧
      ∀ d, MatchMM maxpage num_id cb d (hmemR iv.toNat H1) →
        (σ1 "id" = BitVec.ofNat 32 id ∧ ATInv maxpage kl kh d.toPData ∧
          (d.AC id).cusage ≤ (d.AC id).cquota ∧ ∃ d1 r, container_alloc_spec id d = some (d1, r)) →
        ∃ (σ2 : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR) (d' : RData),
          Star (rprimsA εR c) ⟨container_alloc cb maxpage, .stop, σ, l⟩ ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          MatchMM maxpage num_id cb d' (hmemR iv.toNat H3) ∧
          ∃ r, container_alloc_spec id d = some (d', r) ∧ σ2 "r" = BitVec.ofNat 32 r :=
  Triple.locked hE hRR hc hRA hl hidle bound K hK hF σ hσ
    (container_alloc_triple εR c iv.toNat hmax hcb hnum id hid)


/-! ## The getters (`MALTCSource.v`) -/

/-- `return container_LOC[id].field;` for field `f`: 0 quota, 1 usage, 2 parent, 3 nchildren. -/
def getterCS (cb : Nat) (f : Val) : Stmt APrim := .call "r" .pull [lkE, ccellE cb "id" f]

def getter (cb : Nat) (f : Val) : Stmt APrim := .seq acquireA (.seq (getterCS cb f) relA)

/-- **A getter returns the field** of the table the previous holder released,
and releases the table unchanged. With `get_quota_ref`, `get_usage_ref`,
`get_parent_ref` and `get_nchildren_ref` this is refinement of
`container_get_quota_spec` and the other three. -/
theorem getter_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (cb : Nat) (f : Val) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨getter cb f, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = hmemR iv.toNat H1 ∧ σ' "r" = hmemR iv.toNat H1 (ccell cb (σ "id") f) := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hfr, hR1, hR2⟩ :=
    cs_guarantee1 hE hRR hc hRA hl hidle bound K hK hF σ hσ (getterCS cb f)
      (fun b σ b' σ' => b' = b ∧ σ' "r" = b (ccell cb (σ "id") f))
      (fun σ l b hlk hcs => ⟨σ.set "r" (b (ccell cb (σ "id") f)), l, b,
        cs1_rd hcs (by rw [hlk]) "r" (ccellE cb "id" f), hcs,
        by rw [Locals.set_other _ _ (by decide)]; exact hlk, rfl, by simp⟩)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hR1, ?_⟩
  rw [Locals.set_other _ _ (by decide), hR2, hfr "id" (by decide) (by decide) (by decide) (by decide)]

/-! ## `container_split` -/

/-- The child slot: `id * MAX_CHILDREN + 1 + nc`. -/
def childC (cb : Nat) (mc : Val) (b : Region) (id : Val) : Val := id * mc + 1 + b (ccell cb id 3)

/-- What `container_split(id, q)` does to the table, and the child it returns. -/
def ctSplitC (cb : Nat) (mc : Val) (b : Region) (id q : Val) : Region × Val :=
  let ch := childC cb mc b id
  let b5 := setCell (setCell (setCell (setCell (setCell b (ccell cb ch 4) 1) (ccell cb ch 0) q) (ccell cb ch 1) 0)
    (ccell cb ch 2) id) (ccell cb ch 3) 0
  (setCell (setCell b5 (ccell cb id 1) (b5 (ccell cb id 1) + q)) (ccell cb id 3) (b (ccell cb id 3) + 1), ch)

/-- ```
nc = CT[id].nchildren; ch = id * MAX_CHILDREN + 1 + nc;
CT[ch].used = 1; CT[ch].quota = quota; CT[ch].usage = 0; CT[ch].parent = id; CT[ch].nchildren = 0;
CT[id].usage += quota; CT[id].nchildren = nc + 1; return ch;
``` -/
def ctSplitCS (cb : Nat) (mcv : Val) : Stmt APrim :=
  .seq (.call "nc" .pull [lkE, ccellE cb "id" 3])
  (.seq (.assign "ch" (.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv)) (.const 1)) (.var "nc")))
  (.seq (.call "_" .push [lkE, ccellE cb "ch" 4, .const 1])
  (.seq (.call "_" .push [lkE, ccellE cb "ch" 0, .var "amt"])
  (.seq (.call "_" .push [lkE, ccellE cb "ch" 1, .const 0])
  (.seq (.call "_" .push [lkE, ccellE cb "ch" 2, .var "id"])
  (.seq (.call "_" .push [lkE, ccellE cb "ch" 3, .const 0])
  (.seq (.call "u" .pull [lkE, ccellE cb "id" 1])
  (.seq (.call "_" .push [lkE, ccellE cb "id" 1, .bin .add (.var "u") (.var "amt")])
  (.seq (.call "_" .push [lkE, ccellE cb "id" 3, .bin .add (.var "nc") (.const 1)])
    (.assign "r" (.var "ch")))))))))))

def container_split (cb : Nat) (mcv : Val) : Stmt APrim := .seq acquireA (.seq (ctSplitCS cb mcv) relA)

theorem wr1 {εR : REnv} {c : CPU} {i : Nat} {cb : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (y : Ident) (f : Val) (ve : Expr) {id v : Val} (hy : σ y = id)
    (hv : ve.eval σ = v) :
    ∃ l', Runs (rprimsA εR c) (.call "_" .push [lkE, ccellE cb y f, ve]) σ l (σ.set "_" 0) l' ∧
      CS1 c i l' (setCell b (ccell cb id f) v) := by
  subst hy hv; exact cs1_wr h hlk (ccellE cb y f) ve

theorem set_self {σ : Locals} {x : Ident} {v : Val} (h : σ x = v) : σ.set x v = σ := by
  funext y; by_cases e : y = x
  · subst e; simp [h]
  · simp [Locals.set, e]

/-- **The body of `container_split` computes `ctSplitC`.** -/
theorem ctSplitCS_run (εR : REnv) {c : CPU} {i : Nat} (cb : Nat) (mcv : Val) (σ : Locals) (l : RLog) (b : Region)
    (hlk : (σ "lk").toNat = i) (hcs : CS1 c i l b) :
    ∃ σ' l', Runs (rprimsA εR c) (ctSplitCS cb mcv) σ l σ' l' ∧
      CS1 c i l' (ctSplitC cb mcv b (σ "id") (σ "amt")).1 ∧ σ' "lk" = σ "lk" ∧
      σ' "r" = (ctSplitC cb mcv b (σ "id") (σ "amt")).2 := by
  let ID := σ "id"
  let Q := σ "amt"
  let NC := b (ccell cb ID 3)
  let CH := childC cb mcv b ID
  let σ0 := σ.set "nc" NC
  let σ1 := σ0.set "ch" CH
  let σ2 := σ1.set "_" 0
  have h0 : Runs (rprimsA εR c) (.call "nc" .pull [lkE, ccellE cb "id" 3]) σ l σ0 l :=
    cs1_rd hcs hlk "nc" (ccellE cb "id" 3)
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
  let B5 := setCell (setCell (setCell (setCell (setCell b (ccell cb CH 4) 1) (ccell cb CH 0) Q) (ccell cb CH 1) 0)
    (ccell cb CH 2) ID) (ccell cb CH 3) 0
  let σ3 := σ2.set "u" (B5 (ccell cb ID 1))
  have h6 : Runs (rprimsA εR c) (.call "u" .pull [lkE, ccellE cb "id" 1]) σ2 l5 σ3 l5 := by
    have h := cs1_rd (εR := εR) c5 hlk2 "u" (ccellE cb "id" 1)
    have e : ((ccellE cb "id" 1).eval σ2).toNat = ccell cb ID 1 := by show ccell cb (σ2 "id") 1 = _; rw [hid2]
    rw [e] at h; exact h
  have hlk3 : (σ3 "lk").toNat = i := by simpa [σ3, Locals.set] using hlk2
  have hid3 : σ3 "id" = ID := by simp [σ3, Locals.set, hid2]
  obtain ⟨l7, w7, c7⟩ := wr1 (εR := εR) c5 hlk3 "id" 1 (.bin .add (.var "u") (.var "amt")) hid3
    (v := B5 (ccell cb ID 1) + Q) (by simp [Expr.eval, BinOp.eval, σ3, σ2, σ1, σ0, Locals.set, Q])
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

set_option maxHeartbeats 3200000 in
/-- **`container_split` refines `container_split_spec`.** The C code makes no
checks. The specification's conditions (the container is in use, the child
slot is in range, there is room for another child, the quota is available)
are what make its writes land on the right cells. -/
theorem split_ref {num_id cb mc : Nat} (hnum : cb + 5 * num_id < 2 ^ 32) {d d' : RData} {b : Region} {id q r : Nat}
    (hC : MatchC num_id cb d.AC b) (hid : id < num_id)
    (h : container_split_spec num_id mc id q d = some (d', r)) :
    MatchC num_id cb d'.AC (ctSplitC cb (BitVec.ofNat 32 mc) b (BitVec.ofNat 32 id) (BitVec.ofNat 32 q)).1 ∧
    (ctSplitC cb (BitVec.ofNat 32 mc) b (BitVec.ofNat 32 id) (BitVec.ofNat 32 q)).2 = BitVec.ofNat 32 r := by
  unfold container_split_spec at h
  simp only at h
  by_cases hc : (d.AC id).cused = true ∧ id * mc + 1 + (d.AC id).cchildren.length < num_id ∧
      (d.AC id).cchildren.length < mc ∧ q + (d.AC id).cusage ≤ (d.AC id).cquota
  · rw [if_pos hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hused, hilt, hLmc, hqu⟩ := hc
    obtain ⟨hq, hus, hpa, hnc, hud⟩ := hC.used hid hused
    have hmul : id ≤ id * mc := Nat.le_mul_of_pos_right _ (by omega)
    have hq32 : q < 2 ^ 32 := by have := (b (cb + 5 * id)).isLt; omega
    have hch : childC cb (BitVec.ofNat 32 mc) b (BitVec.ofNat 32 id) =
        BitVec.ofNat 32 (id * mc + 1 + (d.AC id).cchildren.length) := by
      unfold childC
      rw [cell3 hnum hid, val_of_toNat hnc (by omega)]
      simp [BitVec.ofNat_add, BitVec.ofNat_mul]
    unfold ctSplitC
    simp only [hch, cell0 hnum hilt, cell1 hnum hilt, cell2 hnum hilt, cell3 hnum hilt, cell4 hnum hilt,
      cell1 hnum hid, cell3 hnum hid]
    refine ⟨fun j hj => ?_, trivial⟩
    by_cases hjI : j = id * mc + 1 + (d.AC id).cchildren.length
    · rw [hjI, setAt_eq]
      simp (disch := omega) only [setCell, if_pos, if_neg, ↓reduceIte]
      unfold MatchCont
      rw [if_pos rfl]
      refine ⟨?_, rfl, ?_, rfl, rfl⟩
      · simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hq32
      · simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    · rw [setAt_ne _ _ hjI]
      by_cases hji : j = id
      · rw [hji, setAt_eq]
        simp (disch := omega) only [setCell, if_pos, if_neg, ↓reduceIte]
        unfold MatchCont
        simp only
        rw [if_pos hused]
        refine ⟨hq, ?_, hpa, ?_, hud⟩
        · have hb := (b (cb + 5 * id)).isLt
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        · have h1 : (1 : Val).toNat = 1 := rfl
          simp only [BitVec.toNat_add, List.length_cons, h1]; omega
      · rw [setAt_ne _ _ hji]
        simp (disch := omega) only [setCell, if_pos, if_neg, ↓reduceIte]
        exact hC j hj
  · rw [if_neg hc] at h; cases h

theorem ctSplitCS_fr (cb : Nat) (mcv : Val) : frS "lk" (ctSplitCS cb mcv) = true := by simp [frS, ctSplitCS]

/-- **`container_split(id, amt)` refines `container_split_spec`.** -/
theorem container_split_refines {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {num_id cb : Nat} (hnum : cb + 5 * num_id < 2 ^ 32) (mc : Nat) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨container_split cb (BitVec.ofNat 32 mc), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (ctSplitC cb (BitVec.ofNat 32 mc) (hmemR iv.toNat H1) (σ "id") (σ "amt")).1 ∧
      ∀ (d d' : RData) (id q r : Nat), σ "id" = BitVec.ofNat 32 id → σ "amt" = BitVec.ofNat 32 q →
        id < num_id → MatchC num_id cb d.AC (hmemR iv.toNat H1) →
        container_split_spec num_id mc id q d = some (d', r) →
        MatchC num_id cb d'.AC (hmemR iv.toNat H3) ∧ σ' "r" = BitVec.ofNat 32 r := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hfr, hR1, hR2⟩ :=
    cs_guarantee1 hE hRR hc hRA hl hidle bound K hK hF σ hσ (ctSplitCS cb (BitVec.ofNat 32 mc))
      (fun b σ b' σ' => b' = (ctSplitC cb (BitVec.ofNat 32 mc) b (σ "id") (σ "amt")).1 ∧
        σ' "r" = (ctSplitC cb (BitVec.ofNat 32 mc) b (σ "id") (σ "amt")).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', hr, hc', hlk', hres⟩ := ctSplitCS_run εR cb (BitVec.ofNat 32 mc) σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, rfl, hres⟩)
  have hd := hfr "id" (by decide) (by decide) (by decide) (by decide)
  have ha := hfr "amt" (by decide) (by decide) (by decide) (by decide)
  have hm : hmemR iv.toNat H3 = (ctSplitC cb (BitVec.ofNat 32 mc) (hmemR iv.toNat H1) (σ "id") (σ "amt")).1 := by
    rw [hR1, hd, ha]
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hm, fun d d' id q r hsid hsq hlt hC hs => ?_⟩
  obtain ⟨g1, g2⟩ := split_ref hnum hC hlt hs
  refine ⟨by rw [hm, hsid, hsq]; exact g1, ?_⟩
  rw [Locals.set_other _ _ (by decide), hR2, hd, ha, hsid, hsq]; exact g2

end MContainer
