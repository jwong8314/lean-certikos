import CertiKOS.KernPT

/-!
# Kernel, memory management: containers (memory quotas)

The third kernel module: mCertiKOS's `MContainer` (`mcertikos/mm`). Each
process has a **container** that records how many pages it may use (`quota`),
how many it has used (`usage`), its parent, how many children it has, and
whether the slot is in use. A child's quota is carved out of its parent's.

The container table is a region protected by one lock. Container `id` is the
record of five cells starting at `id * 5`.

* `nest`, `nest_run`: calling lock-only code on another lock from inside a
  critical section. We keep our lock and our region.
* `ctAllocSpec`, `ctAlloc_guarantee`: **`container_alloc`.** If the container
  is under quota, call `palloc` (on the allocation table's lock) and charge
  one page if it succeeded.
* `ctFreeSpec`, `ctFree_guarantee`: **`container_free`.** Give one page back
  and call `pfree`.
* `ctSplitSpec`, `ctSplit_guarantee`: **`container_split`.** If the parent has
  `amt` pages left, set up a child with quota `amt` and charge the parent.
* `alloc_inv`, `free_inv`, `split_inv`: the quota invariant `usage ≤ quota`
  is kept. After a split the child has quota `amt`, usage 0 and the right
  parent, and the parent stays within its quota.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace KernContainer

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region setCell hmemR Holding)
open LockRegionCPU KernPAlloc KernFrame
open KernPT (palloc_lk palloc_le setCell_eq setCell_ne)

/-! ## Calling code on another lock from inside a critical section -/

/-- `plk = lk; lk = j; s; lk = plk;` -/
def nest (jv : Val) (s : Stmt APrim) : Stmt APrim :=
  .seq (.assign "plk" lkE) (.seq (.assign "lk" (.const jv)) (.seq s (.assign "lk" (.var "plk"))))

/-- **A nested call keeps our lock and region.** `s` works only on the lock in
`lk` and ends idle on it. -/
theorem nest_run {εR : REnv} {c : CPU} {s : Stmt APrim} (hL : LkS s) (hf : frS "lk" s = true)
    (hfp : frS "plk" s = true) {jv : Val} {i : Nat} (hi : i ≠ jv.toNat) {σ : Locals} {l : RLog}
    {b : Region} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hh : Holding S c i)
    (hb : S.mem i = b) {σp : Locals} {rb : RLog} {S3 : RState} {H3 : HLogR}
    (hrun : Star (rprimsA εR c) ⟨s, .stop, (σ.set "plk" (σ "lk")).set "lk" jv, l⟩ ⟨.skip, .stop, σp, rb⟩)
    (hl3 : rreplay rb = some (S3, H3)) (hid3 : (S3.lk jv.toNat).phase c = .idle) :
    Runs (rprimsA εR c) (nest jv s) σ l (σp.set "lk" (σ "lk")) rb ∧ CSt c i jv.toNat rb b := by
  have hR : Runs (rprimsA εR c) s ((σ.set "plk" (σ "lk")).set "lk" jv) l σp rb := Runs.of_stop hrun
  have hext : Ext c jv.toNat l rb := by
    have := lk_star hrun hL trivial hf rfl
    simpa using this
  obtain ⟨f1, f2⟩ := ext_frame' hi hl hl3 hext
  have hplk : σp "plk" = σ "lk" := by rw [hR.frame hfp]; simp [Locals.set]
  refine ⟨?_, S3, H3, hl3, ?_, hid3, (f2 hh).trans hb⟩
  · have h := Runs.assign (P := rprimsA εR c) (σ := σp) (l := rb) "lk" (.var "plk")
    have he : (Expr.var "plk").eval σp = σ "lk" := hplk
    rw [he] at h
    exact Runs.seq (Runs.assign _ _) (Runs.seq (Runs.assign _ _) (Runs.seq hR h))
  · obtain ⟨t, ht⟩ := hh; exact ⟨t, by rw [f1]; exact ht⟩

/-! ## The container table -/

/-- Cell `f` of the container `id`: 0 quota, 1 usage, 2 parent, 3 number of children, 4 in use. -/
def cell (id f : Val) : Nat := (id * 5 + f).toNat

/-- `x * 5 + f` -/
def cellE (x : Ident) (f : Val) : Expr := .bin .add (.bin .mul (.var x) (.const 5)) (.const f)

/-- **The abstract `container_alloc`.** `p` is the page `palloc` returns
(`np` when none is free). The result is the page, or `np`. -/
def ctAllocSpec (np : Nat) (b : Region) (p : Nat) (id : Val) : Region × Nat :=
  if (b (cell id 1)).ult (b (cell id 0)) then
    (if p = np then (b, np) else (setCell b (cell id 1) (b (cell id 1) + 1), p))
  else (b, np)

/-- **The abstract `container_free`**: give one page back. -/
def ctFreeSpec (b : Region) (id : Val) : Region :=
  if b (cell id 1) = 0 then b else setCell b (cell id 1) (b (cell id 1) - 1)

/-- The child slot `container_split` uses. -/
def childOf (mc : Val) (b : Region) (id : Val) : Val := id * mc + 1 + b (cell id 3)

/-- **The abstract `container_split`.** If the parent has `amt` pages left, set
up the child and charge the parent. The result is the child, or 0. -/
def ctSplitSpec (mc : Val) (b : Region) (id amt : Val) : Region × Val :=
  if (b (cell id 0) - b (cell id 1)).ult amt then (b, 0)
  else
    let ch := childOf mc b id
    (setCell (setCell (setCell (setCell (setCell (setCell (setCell b (cell ch 4) 1) (cell ch 0) amt)
      (cell ch 1) 0) (cell ch 2) id) (cell ch 3) 0) (cell id 1) (b (cell id 1) + amt))
      (cell id 3) (b (cell id 3) + 1), ch)

/-! ## The C code -/

/-- `u = CT[id].usage; q = CT[id].quota; if (u < q) { r = palloc(); if (r != np) CT[id].usage = u + 1; } else r = np;` -/
def ctAllocCS (atv npv : Val) : Stmt APrim :=
  .seq (.call "u" .pull [lkE, cellE "id" 1]) (.seq (.call "q" .pull [lkE, cellE "id" 0])
    (.ite (.bin .ltu (.var "u") (.var "q"))
      (.seq (nest atv (palloc npv)) (.ite (.bin .ne (.var "r") (.const npv))
        (.call "_" .push [lkE, cellE "id" 1, .bin .add (.var "u") (.const 1)]) .skip))
      (.assign "r" (.const npv))))

def ctAlloc (atv npv : Val) : Stmt APrim := .seq acquireA (.seq (ctAllocCS atv npv) relA)

/-- `u = CT[id].usage; if (u != 0) CT[id].usage = u - 1; pfree(j);` -/
def ctFreeCS (atv : Val) : Stmt APrim :=
  .seq (.call "u" .pull [lkE, cellE "id" 1])
    (.seq (.ite (.bin .ne (.var "u") (.const 0))
        (.call "_" .push [lkE, cellE "id" 1, .bin .sub (.var "u") (.const 1)]) .skip)
      (nest atv pfree))

def ctFree (atv : Val) : Stmt APrim := .seq acquireA (.seq (ctFreeCS atv) relA)

/-- The writes of `container_split`. -/
def splitBody (mcv : Val) : Stmt APrim :=
  .seq (.assign "ch" (.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv)) (.const 1)) (.var "nc")))
  (.seq (.call "_" .push [lkE, cellE "ch" 4, .const 1])
  (.seq (.call "_" .push [lkE, cellE "ch" 0, .var "amt"])
  (.seq (.call "_" .push [lkE, cellE "ch" 1, .const 0])
  (.seq (.call "_" .push [lkE, cellE "ch" 2, .var "id"])
  (.seq (.call "_" .push [lkE, cellE "ch" 3, .const 0])
  (.seq (.call "_" .push [lkE, cellE "id" 1, .bin .add (.var "u") (.var "amt")])
  (.seq (.call "_" .push [lkE, cellE "id" 3, .bin .add (.var "nc") (.const 1)])
    (.assign "r" (.var "ch")))))))))

/-- `u = usage; q = quota; nc = nchildren; if (q - u < amt) r = 0; else { ch = id * mc + 1 + nc; <set up ch>; usage = u + amt; nchildren = nc + 1; r = ch; }` -/
def ctSplitCS (mcv : Val) : Stmt APrim :=
  .seq (.call "u" .pull [lkE, cellE "id" 1]) (.seq (.call "q" .pull [lkE, cellE "id" 0])
    (.seq (.call "nc" .pull [lkE, cellE "id" 3])
      (.ite (.bin .ltu (.bin .sub (.var "q") (.var "u")) (.var "amt")) (.assign "r" (.const 0)) (splitBody mcv))))

def ctSplit (mcv : Val) : Stmt APrim := .seq acquireA (.seq (ctSplitCS mcv) relA)

/-! ## The critical sections compute the specifications -/

theorem rd_cell {εR : REnv} {c : CPU} {i j : Nat} {l : RLog} {b : Region} (h : CSt c i j l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (x y : Ident) (f : Val) {id : Val} (hy : σ y = id) :
    Runs (rprimsA εR c) (.call x .pull [lkE, cellE y f]) σ l (σ.set x (b (cell id f))) l := by
  subst hy; exact cst_rd h hlk x (cellE y f)

theorem wr_cell {εR : REnv} {c : CPU} {i j : Nat} {l : RLog} {b : Region} (h : CSt c i j l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (y : Ident) (f : Val) (ve : Expr) {id : Val} (hy : σ y = id) :
    ∃ l', Runs (rprimsA εR c) (.call "_" .push [lkE, cellE y f, ve]) σ l (σ.set "_" 0) l' ∧
      CSt c i j l' (setCell b (cell id f) (ve.eval σ)) := by
  subst hy; exact cst_wr h hlk (cellE y f) ve

theorem ltu_true {σ : Locals} {a b : Expr} (h : (a.eval σ).ult (b.eval σ) = true) :
    ¬ (Expr.bin .ltu a b).eval σ = 0 := by simp [Expr.eval, BinOp.eval, h]

theorem ltu_false {σ : Locals} {a b : Expr} (h : ¬ (a.eval σ).ult (b.eval σ) = true) :
    (Expr.bin .ltu a b).eval σ = 0 := by simp [Expr.eval, BinOp.eval, h]

theorem palloc_fr (npv : Val) (z : Ident) (h1 : z ≠ "t") (h2 : z ≠ "n") (h3 : z ≠ "_") (h4 : z ≠ "v")
    (h5 : z ≠ "i") (h6 : z ≠ "r") (h7 : z ≠ "x") : frS z (palloc npv) = true := by
  simp [frS, palloc, acquireA, loopA, pallocCS, scanLoop, scanBody, relA, Ne.symm h1, Ne.symm h2,
    Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7]

theorem pfree_fr (z : Ident) (h1 : z ≠ "t") (h2 : z ≠ "n") (h3 : z ≠ "_") (h4 : z ≠ "v") :
    frS z pfree = true := by
  simp [frS, pfree, pfreeCS, acquireA, loopA, relA, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

theorem pfree_lk : LkS pfree := by simp [LkS, pfree, pfreeCS, acquireA, loopA, relA]

/-- **The critical section of `container_alloc` computes `ctAllocSpec`.** -/
theorem ctAllocCS_run {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    {atv : Val} (hF : ∀ tn, LockArray.FairA ε c atv.toNat tn bound) (np : Nat) (hnp : np < 2 ^ 32)
    {i : Nat} (hi : i ≠ atv.toNat) (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i)
    (hcs : CSt c i atv.toNat l b) :
    ∃ σ' l' a, Runs (rprimsA εR c) (ctAllocCS atv (BitVec.ofNat 32 np)) σ l σ' l' ∧
      CSt c i atv.toNat l' (ctAllocSpec np b (pallocSpec np a).2 (σ "id")).1 ∧ σ' "lk" = σ "lk" ∧
      σ' "r" = BitVec.ofNat 32 (ctAllocSpec np b (pallocSpec np a).2 (σ "id")).2 := by
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
  by_cases hlt : U.ult Q = true
  · obtain ⟨S, H, hl, hh, hid, hb⟩ := hcs
    obtain ⟨σp, rb, S3, H1, H3, hrun, hl3, hid3, -, hr⟩ :=
      palloc_guarantee hE hRR hc hRA hl (iv := atv) hid bound K hK (hF _)
        ((σ1.set "plk" (σ1 "lk")).set "lk" atv) (by simp) np hnp
    obtain ⟨hnest, hc2⟩ := nest_run (palloc_lk _)
      (palloc_fr _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (palloc_fr _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hi hl hh hb hrun hl3 hid3
    have hfr : ∀ z : Ident, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → z ≠ "i" → z ≠ "r" → z ≠ "x" →
        σp z = ((σ1.set "plk" (σ1 "lk")).set "lk" atv) z := fun z h1 h2 h3 h4 h5 h6 h7 =>
      (Runs.of_stop hrun).frame (palloc_fr _ z h1 h2 h3 h4 h5 h6 h7)
    let σ2 := σp.set "lk" (σ1 "lk")
    have hr2 : σ2 "r" = BitVec.ofNat 32 (pallocSpec np (hmemR atv.toNat H1)).2 := by
      simp [σ2, Locals.set, hr]
    have hlk2 : σ2 "lk" = σ "lk" := by simp [σ2, hlk1]
    have hid2 : σ2 "id" = σ "id" := by
      simp only [σ2, Locals.set_other _ _ (show ("id" : Ident) ≠ "lk" by decide)]
      rw [hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [Locals.set, hid1]
    have hu2 : σ2 "u" = U := by
      simp only [σ2, Locals.set_other _ _ (show ("u" : Ident) ≠ "lk" by decide)]
      rw [hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [Locals.set, hu1]
    have hguard : ¬ (Expr.bin .ltu (.var "u") (.var "q")).eval σ1 = 0 :=
      ltu_true (by simp only [Expr.eval]; rw [hu1, hq1]; exact hlt)
    by_cases hp : (pallocSpec np (hmemR atv.toNat H1)).2 = np
    · refine ⟨σ2, rb, hmemR atv.toNat H1, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_true hguard
        (Runs.seq hnest (Runs.ite_false (ne_false (hr2.trans (by rw [hp]))) Runs.skip)))), ?_, hlk2, ?_⟩
      · have : ctAllocSpec np b (pallocSpec np (hmemR atv.toNat H1)).2 (σ "id") = (b, np) := by
          rw [ctAllocSpec, if_pos hlt, if_pos hp]
        rw [this]; exact hc2
      · have : ctAllocSpec np b (pallocSpec np (hmemR atv.toNat H1)).2 (σ "id") = (b, np) := by
          rw [ctAllocSpec, if_pos hlt, if_pos hp]
        rw [this, hr2, hp]
    · have hple := palloc_le np (hmemR atv.toNat H1)
      obtain ⟨l3, hw, hc3⟩ := wr_cell (εR := εR) hc2 (σ := σ2) (by rw [hlk2]; exact hlk) "id" 1
        (.bin .add (.var "u") (.const 1)) hid2
      have hev : (Expr.bin .add (.var "u") (.const 1)).eval σ2 = U + 1 := by
        simp only [Expr.eval, BinOp.eval]; rw [hu2]
      rw [hev] at hc3
      have hspec : ctAllocSpec np b (pallocSpec np (hmemR atv.toNat H1)).2 (σ "id") =
          (setCell b (cell (σ "id") 1) (U + 1), (pallocSpec np (hmemR atv.toNat H1)).2) := by
        rw [ctAllocSpec, if_pos hlt, if_neg hp]
      refine ⟨σ2.set "_" 0, l3, hmemR atv.toNat H1, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_true hguard
        (Runs.seq hnest (Runs.ite_true (ne_true (fun h => ofNat_ne (by omega) hnp hp (hr2.symm.trans h))) hw)))),
        ?_, ?_, ?_⟩
      · rw [hspec]; exact hc3
      · rw [Locals.set_other _ _ (by decide)]; exact hlk2
      · rw [hspec, Locals.set_other _ _ (by decide)]; exact hr2
  · have hguard : (Expr.bin .ltu (.var "u") (.var "q")).eval σ1 = 0 :=
      ltu_false (by simp only [Expr.eval]; rw [hu1, hq1]; exact hlt)
    have hspec : ctAllocSpec np b (pallocSpec np (fun _ => 0)).2 (σ "id") = (b, np) := by
      rw [ctAllocSpec, if_neg hlt]
    refine ⟨σ1.set "r" (BitVec.ofNat 32 np), l, fun _ => 0, Runs.seq hr0 (Runs.seq hr1
      (Runs.ite_false hguard (Runs.assign _ _))), ?_, ?_, ?_⟩
    · rw [hspec]; exact hcs
    · rw [Locals.set_other _ _ (by decide)]; exact hlk1
    · rw [hspec]; simp

/-- **The critical section of `container_free` computes `ctFreeSpec`.** -/
theorem ctFreeCS_run {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    {atv : Val} (hF : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    {i : Nat} (hi : i ≠ atv.toNat) (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i)
    (hcs : CSt c i atv.toNat l b) :
    ∃ σ' l', Runs (rprimsA εR c) (ctFreeCS atv) σ l σ' l' ∧
      CSt c i atv.toNat l' (ctFreeSpec b (σ "id")) ∧ σ' "lk" = σ "lk" := by
  let U := b (cell (σ "id") 1)
  let σ0 := σ.set "u" U
  have hr0 : Runs (rprimsA εR c) (.call "u" .pull [lkE, cellE "id" 1]) σ l σ0 l := rd_cell hcs hlk "u" "id" 1 rfl
  have hlk0 : σ0 "lk" = σ "lk" := by simp [σ0, Locals.set]
  have hu0 : σ0 "u" = U := by simp [σ0]
  -- the usage update
  have hmid : ∃ σ1 l1, Runs (rprimsA εR c) (.ite (.bin .ne (.var "u") (.const 0))
      (.call "_" .push [lkE, cellE "id" 1, .bin .sub (.var "u") (.const 1)]) .skip) σ0 l σ1 l1 ∧
      CSt c i atv.toNat l1 (ctFreeSpec b (σ "id")) ∧ σ1 "lk" = σ "lk" := by
    by_cases hz : U = 0
    · refine ⟨σ0, l, Runs.ite_false (ne_false (hu0.trans hz)) Runs.skip, ?_, hlk0⟩
      have : ctFreeSpec b (σ "id") = b := if_pos hz
      rw [this]; exact hcs
    · obtain ⟨l1, hw, hc1⟩ := wr_cell (εR := εR) hcs (σ := σ0) (by rw [hlk0]; exact hlk) "id" 1
        (.bin .sub (.var "u") (.const 1)) (id := σ "id") (by simp [σ0, Locals.set])
      have hev : (Expr.bin .sub (.var "u") (.const 1)).eval σ0 = U - 1 := by
        simp only [Expr.eval, BinOp.eval]; rw [hu0]
      rw [hev] at hc1
      refine ⟨σ0.set "_" 0, l1, Runs.ite_true (ne_true (by rw [hu0]; exact hz)) hw, ?_, ?_⟩
      · have : ctFreeSpec b (σ "id") = setCell b (cell (σ "id") 1) (U - 1) := if_neg hz
        rw [this]; exact hc1
      · rw [Locals.set_other _ _ (by decide)]; exact hlk0
  obtain ⟨σ1, l1, hm, ⟨S, H, hl, hh, hid, hb⟩, hlk1⟩ := hmid
  obtain ⟨σp, rb, S3, H1, H3, hrun, hl3, hid3, -⟩ :=
    pfree_guarantee hE hRR hc hRA hl (iv := atv) hid bound K hK (hF _)
      ((σ1.set "plk" (σ1 "lk")).set "lk" atv) (by simp)
  obtain ⟨hnest, hc2⟩ := nest_run pfree_lk (pfree_fr _ (by decide) (by decide) (by decide) (by decide))
    (pfree_fr _ (by decide) (by decide) (by decide) (by decide)) hi hl hh hb hrun hl3 hid3
  exact ⟨_, rb, Runs.seq hr0 (Runs.seq hm hnest), hc2, by simp [hlk1]⟩

/-- **The critical section of `container_split` computes `ctSplitSpec`.** -/
theorem ctSplitCS_run (εR : REnv) {c : CPU} {i j : Nat} (mcv : Val) (σ : Locals) (l : RLog) (b : Region)
    (hlk : (σ "lk").toNat = i) (hcs : CSt c i j l b) :
    ∃ σ' l', Runs (rprimsA εR c) (ctSplitCS mcv) σ l σ' l' ∧
      CSt c i j l' (ctSplitSpec mcv b (σ "id") (σ "amt")).1 ∧ σ' "lk" = σ "lk" ∧
      σ' "r" = (ctSplitSpec mcv b (σ "id") (σ "amt")).2 := by
  let U := b (cell (σ "id") 1)
  let Q := b (cell (σ "id") 0)
  let NC := b (cell (σ "id") 3)
  let σ0 := σ.set "u" U
  let σ1 := σ0.set "q" Q
  let σ2 := σ1.set "nc" NC
  have hr0 : Runs (rprimsA εR c) (.call "u" .pull [lkE, cellE "id" 1]) σ l σ0 l := rd_cell hcs hlk "u" "id" 1 rfl
  have hr1 : Runs (rprimsA εR c) (.call "q" .pull [lkE, cellE "id" 0]) σ0 l σ1 l :=
    rd_cell hcs (σ := σ0) (by simp [σ0, Locals.set, hlk]) "q" "id" 0 (by simp [σ0, Locals.set])
  have hr2 : Runs (rprimsA εR c) (.call "nc" .pull [lkE, cellE "id" 3]) σ1 l σ2 l :=
    rd_cell hcs (σ := σ1) (by simp [σ1, σ0, Locals.set, hlk]) "nc" "id" 3 (by simp [σ1, σ0, Locals.set])
  have hgv : (Expr.bin .sub (.var "q") (.var "u")).eval σ2 = Q - U := by
    simp [Expr.eval, BinOp.eval, σ2, σ1, σ0, Locals.set]
  have hamt : (Expr.var "amt").eval σ2 = σ "amt" := by simp [Expr.eval, σ2, σ1, σ0, Locals.set]
  by_cases hlt : (Q - U).ult (σ "amt") = true
  · have hspec : ctSplitSpec mcv b (σ "id") (σ "amt") = (b, 0) := by rw [ctSplitSpec, if_pos hlt]
    refine ⟨σ2.set "r" 0, l, Runs.seq hr0 (Runs.seq hr1 (Runs.seq hr2 (Runs.ite_true
      (ltu_true (a := .bin .sub (.var "q") (.var "u")) (b := .var "amt") (by rw [hgv, hamt]; exact hlt)) (Runs.assign _ _)))), ?_, ?_, ?_⟩
    · rw [hspec]; exact hcs
    · simp [σ2, σ1, σ0, Locals.set]
    · rw [hspec]; simp
  · let CH : Val := childOf mcv b (σ "id")
    let s3 := σ2.set "ch" CH
    have ha : Runs (rprimsA εR c) (.assign "ch" (.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv))
        (.const 1)) (.var "nc"))) σ2 l s3 l := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σ2) (l := l) "ch"
        (.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv)) (.const 1)) (.var "nc"))
      have he : (Expr.bin .add (.bin .add (.bin .mul (.var "id") (.const mcv)) (.const 1)) (.var "nc")).eval σ2
          = CH := by simp [Expr.eval, BinOp.eval, σ2, σ1, σ0, Locals.set, CH, childOf, NC]
      rw [he] at h; exact h
    let s4 := s3.set "_" 0
    have hL : ∀ s : Locals, s = s3 ∨ s = s4 → (s "lk").toNat = i ∧ s "ch" = CH ∧ s "id" = σ "id" ∧
        s "amt" = σ "amt" ∧ s "u" = U ∧ s "nc" = NC := by
      intro s hs
      rcases hs with rfl | rfl <;> simp [s4, s3, σ2, σ1, σ0, Locals.set, hlk]
    have h44 : s4.set "_" 0 = s4 := by
      funext z; simp only [s4, Locals.set]; split <;> simp_all
    obtain ⟨l1, w1, c1⟩ := wr_cell (εR := εR) hcs (hL s3 (.inl rfl)).1 "ch" 4 (.const 1) (hL s3 (.inl rfl)).2.1
    obtain ⟨l2, w2, c2⟩ := wr_cell (εR := εR) c1 (hL s4 (.inr rfl)).1 "ch" 0 (.var "amt") (hL s4 (.inr rfl)).2.1
    obtain ⟨l3, w3, c3⟩ := wr_cell (εR := εR) c2 (hL s4 (.inr rfl)).1 "ch" 1 (.const 0) (hL s4 (.inr rfl)).2.1
    obtain ⟨l4, w4, c4⟩ := wr_cell (εR := εR) c3 (hL s4 (.inr rfl)).1 "ch" 2 (.var "id") (hL s4 (.inr rfl)).2.1
    obtain ⟨l5, w5, c5⟩ := wr_cell (εR := εR) c4 (hL s4 (.inr rfl)).1 "ch" 3 (.const 0) (hL s4 (.inr rfl)).2.1
    obtain ⟨l6, w6, c6⟩ := wr_cell (εR := εR) c5 (hL s4 (.inr rfl)).1 "id" 1
      (.bin .add (.var "u") (.var "amt")) (hL s4 (.inr rfl)).2.2.1
    obtain ⟨l7, w7, c7⟩ := wr_cell (εR := εR) c6 (hL s4 (.inr rfl)).1 "id" 3
      (.bin .add (.var "nc") (.const 1)) (hL s4 (.inr rfl)).2.2.1
    rw [h44] at w2 w3 w4 w5 w6 w7
    have hspec : ctSplitSpec mcv b (σ "id") (σ "amt") =
        (setCell (setCell (setCell (setCell (setCell (setCell (setCell b (cell CH 4) 1) (cell CH 0) (σ "amt"))
          (cell CH 1) 0) (cell CH 2) (σ "id")) (cell CH 3) 0) (cell (σ "id") 1) (U + σ "amt"))
          (cell (σ "id") 3) (NC + 1), CH) := by rw [ctSplitSpec, if_neg hlt]
    obtain ⟨-, hch4, hid4, hamt4, hu4, hnc4⟩ := hL s4 (.inr rfl)
    refine ⟨s4.set "r" CH, l7, Runs.seq hr0 (Runs.seq hr1 (Runs.seq hr2 (Runs.ite_false
      (ltu_false (a := .bin .sub (.var "q") (.var "u")) (b := .var "amt") (by rw [hgv, hamt]; exact hlt))
      (Runs.seq ha (Runs.seq w1 (Runs.seq w2 (Runs.seq w3 (Runs.seq w4 (Runs.seq w5 (Runs.seq w6
        (Runs.seq w7 ?_))))))))))), ?_, ?_, ?_⟩
    · have h := Runs.assign (P := rprimsA εR c) (σ := s4) (l := l7) "r" (.var "ch")
      have he : (Expr.var "ch").eval s4 = CH := hch4
      rw [he] at h; exact h
    · rw [hspec]
      simpa [Expr.eval, BinOp.eval, hid4, hamt4, hu4, hnc4] using c7
    · rw [Locals.set_other _ _ (by decide)]; simp [s4, s3, σ2, σ1, σ0, Locals.set]
    · rw [hspec]; simp

/-! ## The guarantees -/

/-- **`container_alloc` refines `ctAllocSpec`.** It finishes idle on both
locks. The container table it releases, and the page it returns, are
`ctAllocSpec` of the table the previous holder released, with the page that
`palloc` returned on the allocation table `a` it found. -/
theorem ctAlloc_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {atv : Val} (hi : iv.toNat ≠ atv.toNat) (hidat : (S.lk atv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hFat : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    (σ : Locals) (hσ : σ "lk" = iv) (np : Nat) (hnp : np < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR) (a : Region),
      Star (rprimsA εR c) ⟨ctAlloc atv (BitVec.ofNat 32 np), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk atv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (ctAllocSpec np (hmemR iv.toNat H1) (pallocSpec np a).2 (σ "id")).1 ∧
      σ' "r" = BitVec.ofNat 32 (ctAllocSpec np (hmemR iv.toNat H1) (pallocSpec np a).2 (σ "id")).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hidj, hfr, a, hR1, hR2⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle (j := atv.toNat) (fun h => hi h.symm) hidat bound K hK hF σ hσ
      (ctAllocCS atv (BitVec.ofNat 32 np))
      (fun b σ b' σ' => ∃ a, b' = (ctAllocSpec np b (pallocSpec np a).2 (σ "id")).1 ∧
        σ' "r" = BitVec.ofNat 32 (ctAllocSpec np b (pallocSpec np a).2 (σ "id")).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', a, hr, hc', hlk', hres⟩ := ctAllocCS_run hE hRR hc hRA bound K hK hFat np hnp
          hi σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, a, rfl, hres⟩)
  have hd := hfr "id" (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, a, hrun, hl3, hid, hidj, ?_, ?_⟩
  · rw [hR1, hd]
  · rw [Locals.set_other _ _ (by decide), hR2, hd]

/-- **`container_free` refines `ctFreeSpec`**: one page is given back, and
`pfree(j)` has run on the allocation table. -/
theorem ctFree_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {atv : Val} (hi : iv.toNat ≠ atv.toNat) (hidat : (S.lk atv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hFat : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨ctFree atv, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk atv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = ctFreeSpec (hmemR iv.toNat H1) (σ "id") := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hidj, hfr, hR⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle (j := atv.toNat) (fun h => hi h.symm) hidat bound K hK hF σ hσ
      (ctFreeCS atv) (fun b σ b' _ => b' = ctFreeSpec b (σ "id"))
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', hr, hc', hlk'⟩ := ctFreeCS_run hE hRR hc hRA bound K hK hFat hi σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, rfl⟩)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hidj, ?_⟩
  rw [hR, hfr "id" (by decide) (by decide) (by decide) (by decide)]

/-- **`container_split` refines `ctSplitSpec`.** -/
theorem ctSplit_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {j : Nat} (hji : j ≠ iv.toNat) (hidj : (S.lk j).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (mcv : Val) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨ctSplit mcv, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (ctSplitSpec mcv (hmemR iv.toNat H1) (σ "id") (σ "amt")).1 ∧
      σ' "r" = (ctSplitSpec mcv (hmemR iv.toNat H1) (σ "id") (σ "amt")).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, -, hfr, hR1, hR2⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle hji hidj bound K hK hF σ hσ (ctSplitCS mcv)
      (fun b σ b' σ' => b' = (ctSplitSpec mcv b (σ "id") (σ "amt")).1 ∧
        σ' "r" = (ctSplitSpec mcv b (σ "id") (σ "amt")).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', hr, hc', hlk', hres⟩ := ctSplitCS_run εR mcv σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, rfl, hres⟩)
  have hd := hfr "id" (by decide) (by decide) (by decide) (by decide)
  have ha := hfr "amt" (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, ?_, ?_⟩
  · rw [hR1, hd, ha]
  · rw [Locals.set_other _ _ (by decide), hR2, hd, ha]

/-! ## The quota invariant -/

/-- A container stays within its quota. -/
def CInv (b : Region) (id : Val) : Prop := (b (cell id 1)).toNat ≤ (b (cell id 0)).toNat

theorem cell_ne (id : Val) {f g : Val} (h : f ≠ g) : cell id f ≠ cell id g := by
  intro e
  have e' : id * 5 + f = id * 5 + g := BitVec.eq_of_toNat_eq e
  apply h; bv_omega

/-- **`container_alloc` keeps the quota invariant.** -/
theorem alloc_inv (np : Nat) (b : Region) (p : Nat) (id : Val) (hI : CInv b id) :
    CInv (ctAllocSpec np b p id).1 id := by
  unfold ctAllocSpec
  by_cases hlt : (b (cell id 1)).ult (b (cell id 0)) = true
  · rw [if_pos hlt]
    by_cases hp : p = np
    · rw [if_pos hp]; exact hI
    · rw [if_neg hp]
      have h : (b (cell id 1)).toNat < (b (cell id 0)).toNat := BitVec.lt_def.1 (BitVec.ult_iff_lt.1 hlt)
      unfold CInv at hI ⊢
      dsimp only
      rw [setCell_eq, setCell_ne _ _ (cell_ne id (by decide))]
      bv_omega
  · rw [if_neg hlt]; exact hI

/-- **`container_free` keeps the quota invariant.** -/
theorem free_inv (b : Region) (id : Val) (hI : CInv b id) : CInv (ctFreeSpec b id) id := by
  unfold ctFreeSpec
  by_cases hz : b (cell id 1) = 0
  · rw [if_pos hz]; exact hI
  · rw [if_neg hz]
    unfold CInv at hI ⊢
    rw [setCell_eq, setCell_ne _ _ (cell_ne id (by decide))]
    bv_omega

theorem cell_nat {N : Nat} (hN : 5 * N ≤ 2 ^ 32) {a : Val} (ha : a.toNat < N) (f : Val) (hf : f.toNat < 5) :
    cell a f = a.toNat * 5 + f.toNat := by
  unfold cell; bv_omega

/-- **`container_split` sets up the child and keeps the parent within its
quota.** `N` bounds the container ids, and the child slot is a valid id other
than the parent. -/
theorem split_inv {N : Nat} (hN : 5 * N ≤ 2 ^ 32) (mc : Val) (b : Region) (id amt : Val)
    (hid : id.toNat < N) (hch : (childOf mc b id).toNat < N) (hne : childOf mc b id ≠ id)
    (hI : CInv b id) (hok : ¬ (b (cell id 0) - b (cell id 1)).ult amt = true) :
    let b' := (ctSplitSpec mc b id amt).1
    let ch := childOf mc b id
    (ctSplitSpec mc b id amt).2 = ch ∧ CInv b' id ∧ CInv b' ch ∧
    b' (cell id 0) = b (cell id 0) ∧ b' (cell id 1) = b (cell id 1) + amt ∧
    b' (cell ch 0) = amt ∧ b' (cell ch 1) = 0 ∧ b' (cell ch 2) = id ∧ b' (cell ch 4) = 1 := by
  have hnn : (childOf mc b id).toNat ≠ id.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  have hlt : ¬ (b (cell id 0) - b (cell id 1)).toNat < amt.toNat := fun h =>
    hok (BitVec.ult_iff_lt.2 (BitVec.lt_def.2 h))
  have i0 : cell id 0 = id.toNat * 5 + 0 := cell_nat hN hid 0 (by decide)
  have i1 : cell id 1 = id.toNat * 5 + 1 := cell_nat hN hid 1 (by decide)
  have i3 : cell id 3 = id.toNat * 5 + 3 := cell_nat hN hid 3 (by decide)
  have c0 : cell (childOf mc b id) 0 = (childOf mc b id).toNat * 5 + 0 := cell_nat hN hch 0 (by decide)
  have c1 : cell (childOf mc b id) 1 = (childOf mc b id).toNat * 5 + 1 := cell_nat hN hch 1 (by decide)
  have c2 : cell (childOf mc b id) 2 = (childOf mc b id).toNat * 5 + 2 := cell_nat hN hch 2 (by decide)
  have c3 : cell (childOf mc b id) 3 = (childOf mc b id).toNat * 5 + 3 := cell_nat hN hch 3 (by decide)
  have c4 : cell (childOf mc b id) 4 = (childOf mc b id).toNat * 5 + 4 := cell_nat hN hch 4 (by decide)
  have hU : (b (cell id 1) + amt).toNat ≤ (b (cell id 0)).toNat := by
    unfold CInv at hI; bv_omega
  have hspec : ctSplitSpec mc b id amt = (setCell (setCell (setCell (setCell (setCell (setCell (setCell b
      (cell (childOf mc b id) 4) 1) (cell (childOf mc b id) 0) amt) (cell (childOf mc b id) 1) 0)
      (cell (childOf mc b id) 2) id) (cell (childOf mc b id) 3) 0) (cell id 1) (b (cell id 1) + amt))
      (cell id 3) (b (cell id 3) + 1), childOf mc b id) := by rw [ctSplitSpec, if_neg hok]
  simp only [hspec, CInv]
  generalize childOf mc b id = ch at *
  generalize hA : b (cell id 1) + amt = A at *
  generalize b (cell id 3) + 1 = B at *
  rw [i0, i1, i3, c0, c1, c2, c3, c4] at *
  refine ⟨by trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat (first | rw [setCell_eq] | rw [setCell_ne _ _ (by omega)])
  · exact hU
  · exact Nat.zero_le _

end KernContainer
