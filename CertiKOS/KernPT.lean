import CertiKOS.KernFrame

/-!
# Kernel, memory management: page tables

The second kernel module: mCertiKOS's two-level page tables (`MPTIntro`,
`MPTOp`, `MPTCommon` in `mcertikos/mm`).

A **page table** is a region protected by one lock. Its first `nd` cells are
the page directory: entry `d` is 0 when no second-level table is present, and
otherwise holds the address of the table's page. Page `p` has address
`nd + p * ne`, and entry `e` of the table at address `x` is cell `x + e`.
Table pages come from the page allocator (`KernPAlloc.lean`), so inserting a
mapping can call `palloc` while holding the page table's lock.

* `ptInsertSpec`, `ptSet`, `ptLookup`: the abstract operations on the region.
* `ptInsertCS`: the C code of `pt_insert`. It reads the directory entry. If
  the table is missing it calls `palloc` (on the allocation table's lock),
  zeroes the new table page, and installs it. Then it writes the entry.
* `palloc_nested`: `palloc` called while holding another lock keeps that lock
  and its region, by the frame theorem of `KernFrame.lean`.
* `ptInsert_guarantee`: **`pt_insert` refines `ptInsertSpec`.** The page table
  it releases is `ptInsertSpec` of the one the previous holder released, with
  the page the nested `palloc` returned.
* `ptRmv_guarantee`, `ptRead_guarantee`: the same for unmapping an entry and
  for looking one up.
* `PTInv`: the invariant that makes the region a map. Every present directory
  entry is the address of an allocated page, and no two entries share a page.
* `insert_lookup_same`, `insert_lookup_other`, `insert_inv`: under `PTInv`,
  after an insert the new entry reads back, every other entry reads as
  before, and the invariant holds again with the new allocation table.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace KernPT

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region setCell hmemR Holding)
open LockRegionCPU KernPAlloc KernFrame

/-! ## The abstract page table -/

/-- Zero `n` cells from address `x + m` on. -/
def zeroFrom (b : Region) (x : Val) : Nat → Nat → Region
  | _, 0 => b
  | m, n + 1 => zeroFrom (setCell b (x + BitVec.ofNat 32 m).toNat 0) x (m + 1) n

/-- The entry for `(d, e)`: 0 if the second-level table is missing. -/
def ptLookup (b : Region) (d e : Val) : Val := if b d.toNat = 0 then 0 else b (b d.toNat + e).toNat

/-- Write entry `(d, e)` if its table is present. -/
def ptSet (b : Region) (d e v : Val) : Region :=
  if b d.toNat = 0 then b else setCell b (b d.toNat + e).toNat v

/-- Install a zeroed table of `ne` entries at address `x` as directory entry `d`. -/
def ptNew (ne : Nat) (b : Region) (d x : Val) : Region := setCell (zeroFrom b x 0 ne) d.toNat x

/-- The address of page `p`. -/
def pageAddr (ndv nev : Val) (p : Nat) : Val := ndv + BitVec.ofNat 32 p * nev

/-- **The abstract `pt_insert`.** `p` is the page `palloc` returns if the
table is missing (`np` when no page is free). -/
def ptInsertSpec (np : Nat) (ndv : Val) (ne : Nat) (b : Region) (p : Nat) (d e v : Val) : Region :=
  if b d.toNat = 0 then
    if p = np then b else ptSet (ptNew ne b d (pageAddr ndv (BitVec.ofNat 32 ne) p)) d e v
  else ptSet b d e v

/-- The directory entry `pt_insert` ends with: 0 when it failed. -/
def ptInsertRes (np : Nat) (ndv : Val) (ne : Nat) (b : Region) (p : Nat) (d : Val) : Val :=
  if b d.toNat = 0 then (if p = np then 0 else pageAddr ndv (BitVec.ofNat 32 ne) p) else b d.toNat

/-! ## The C code -/

/-- `wr(lk, pd + k, 0); k = k + 1` -/
def zeroBody : Stmt APrim :=
  .seq (.call "_" .push [lkE, .bin .add (.var "pd") (.var "k"), .const 0])
    (.assign "k" (.bin .add (.var "k") (.const 1)))

def zeroLoop (nev : Val) : Stmt APrim := .while (.bin .ne (.var "k") (.const nev)) zeroBody

/-- `palloc()` on the allocation table's lock, from code that uses another lock. -/
def nestPalloc (atv npv : Val) : Stmt APrim :=
  .seq (.assign "plk" lkE) (.seq (.assign "lk" (.const atv)) (.seq (palloc npv) (.assign "lk" (.var "plk"))))

/-- `pd = nd + r * ne; k = 0; while (k != ne) { PT[pd + k] = 0; k++; } PT[d] = pd;` -/
def newTable (ndv nev : Val) : Stmt APrim :=
  .seq (.assign "pd" (.bin .add (.const ndv) (.bin .mul (.var "r") (.const nev))))
    (.seq (.assign "k" (.const 0)) (.seq (zeroLoop nev) (.call "_" .push [lkE, .var "d", .var "pd"])))

/-- `if (pd != 0) PT[pd + e] = w;` -/
def setPTE : Stmt APrim :=
  .ite (.bin .ne (.var "pd") (.const 0)) (.call "_" .push [lkE, .bin .add (.var "pd") (.var "e"), .var "w"]) .skip

/-- `pd = PT[d]; if (pd == 0) { r = palloc(); if (r != np) <new table> } if (pd != 0) PT[pd + e] = w;` -/
def ptInsertCS (atv npv ndv nev : Val) : Stmt APrim :=
  .seq (.call "pd" .pull [lkE, .var "d"])
    (.seq (.ite (.bin .eq (.var "pd") (.const 0))
        (.seq (nestPalloc atv npv) (.ite (.bin .ne (.var "r") (.const npv)) (newTable ndv nev) .skip)) .skip)
      setPTE)

/-- `pt_insert(d, e, w)`: the directory entry is left in `pd` (0 on failure). -/
def ptInsert (atv npv ndv nev : Val) : Stmt APrim := .seq acquireA (.seq (ptInsertCS atv npv ndv nev) relA)

/-- `pd = PT[d]; w = 0; if (pd != 0) PT[pd + e] = w;` -/
def ptRmvCS : Stmt APrim := .seq (.call "pd" .pull [lkE, .var "d"]) (.seq (.assign "w" (.const 0)) setPTE)

def ptRmv : Stmt APrim := .seq acquireA (.seq ptRmvCS relA)

/-- `pd = PT[d]; if (pd != 0) r = PT[pd + e]; else r = 0;` -/
def ptReadCS : Stmt APrim :=
  .seq (.call "pd" .pull [lkE, .var "d"])
    (.ite (.bin .ne (.var "pd") (.const 0)) (.call "r" .pull [lkE, .bin .add (.var "pd") (.var "e")])
      (.assign "r" (.const 0)))

def ptRead : Stmt APrim := .seq acquireA (.seq ptReadCS relA)

/-! ## The critical sections compute the specifications -/

/-- The zeroing loop. -/
theorem zero_run (εR : REnv) (c : CPU) (i j ne : Nat) (hne : ne < 2 ^ 32) :
    ∀ (n m : Nat), m + n = ne → ∀ (σ : Locals) (l : RLog) (b : Region), σ "k" = BitVec.ofNat 32 m →
      (σ "lk").toNat = i → CSt c i j l b →
      ∃ σ' l', Runs (rprimsA εR c) (zeroLoop (BitVec.ofNat 32 ne)) σ l σ' l' ∧
        CSt c i j l' (zeroFrom b (σ "pd") m n)
  | 0, m, hm, σ, l, b, hk, _, hc => by
    have : m = ne := by omega
    subst this
    exact ⟨σ, l, Runs.while_false (ne_false hk), hc⟩
  | n + 1, m, hm, σ, l, b, hk, hlk, hc => by
    have hmlt : m < 2 ^ 32 := by omega
    have hg : σ "k" ≠ BitVec.ofNat 32 ne := by rw [hk]; exact ofNat_ne hmlt hne (by omega)
    obtain ⟨l1, hw, hc1⟩ := cst_wr (εR := εR) hc hlk (.bin .add (.var "pd") (.var "k")) (.const 0)
    let σ1 := σ.set "_" 0
    let σ2 := σ1.set "k" (BitVec.ofNat 32 (m + 1))
    have hk2 : σ2 "k" = BitVec.ofNat 32 (m + 1) := by simp [σ2]
    have hlk2 : (σ2 "lk").toNat = i := by simp [σ2, σ1, Locals.set, hlk]
    have hpd2 : σ2 "pd" = σ "pd" := by simp [σ2, σ1, Locals.set]
    obtain ⟨σ', l', hrun, hc'⟩ := zero_run εR c i j ne hne n (m + 1) (by omega) σ2 l1 _ hk2 hlk2 hc1
    refine ⟨σ', l', Runs.while_true (ne_true hg) (Runs.seq hw ?_) hrun, ?_⟩
    · have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l1) "k" (.bin .add (.var "k") (.const 1))
      have he : (Expr.bin .add (.var "k") (.const 1)).eval σ1 = BitVec.ofNat 32 (m + 1) := by
        simp [Expr.eval, BinOp.eval, σ1, Locals.set, hk, BitVec.ofNat_add]
      rw [he] at h; exact h
    · rw [hpd2] at hc'; simpa [zeroFrom, Expr.eval, BinOp.eval, hk] using hc'

theorem palloc_lk (npv : Val) : LkS (palloc npv) := by
  simp [LkS, palloc, acquireA, loopA, pallocCS, scanLoop, scanBody, relA]

theorem palloc_le (np : Nat) (a : Region) : (pallocSpec np a).2 ≤ np := by
  simp only [pallocSpec, allocFrom]
  cases h : findFree a 0 np with
  | none => exact Nat.le_refl _
  | some j => have := (findFree_some h).2.1; simp only; omega

/-- **`palloc` inside another critical section.** Holding lock `i`, the code
takes the allocation table's lock, allocates and releases. We still hold `i`,
its region is unchanged, and `r` is the page `pallocSpec` returns on the table
`a` that `palloc` found. -/
theorem palloc_nested {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    {atv : Val} (hF : ∀ tn, LockArray.FairA ε c atv.toNat tn bound) (np : Nat) (hnp : np < 2 ^ 32)
    {i : Nat} (hi : i ≠ atv.toNat) {σ : Locals} {l : RLog} {b : Region} (hcs : CSt c i atv.toNat l b) :
    ∃ σ' l' a, Runs (rprimsA εR c) (nestPalloc atv (BitVec.ofNat 32 np)) σ l σ' l' ∧ CSt c i atv.toNat l' b ∧
      σ' "r" = BitVec.ofNat 32 (pallocSpec np a).2 ∧ σ' "lk" = σ "lk" ∧
      σ' "pd" = σ "pd" ∧ σ' "d" = σ "d" ∧ σ' "e" = σ "e" ∧ σ' "w" = σ "w" := by
  obtain ⟨S, H, hl, hh, hid, rfl⟩ := hcs
  let σa := σ.set "plk" (σ "lk")
  let σb := σa.set "lk" atv
  obtain ⟨σp, rb, S3, H1, H3, hrun, hl3, hid3, -, hr⟩ :=
    palloc_guarantee hE hRR hc hRA hl (iv := atv) hid bound K hK (hF _) σb (by simp [σb]) np hnp
  have hR : Runs (rprimsA εR c) (palloc (BitVec.ofNat 32 np)) σb l σp rb := Runs.of_stop hrun
  have hext : Ext c atv.toNat l rb := by
    have := lk_star hrun (palloc_lk _) trivial
      (by simp [frS, palloc, acquireA, loopA, pallocCS, scanLoop, scanBody, relA]) rfl
    simpa [σb] using this
  obtain ⟨f1, f2⟩ := ext_frame' hi hl hl3 hext
  have hfr : ∀ z : Ident, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → z ≠ "i" → z ≠ "r" → z ≠ "x" →
      σp z = σb z := fun z h1 h2 h3 h4 h5 h6 h7 => hR.frame (by
        simp [frS, palloc, acquireA, loopA, pallocCS, scanLoop, scanBody, relA, Ne.symm h1, Ne.symm h2,
          Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7])
  refine ⟨σp.set "lk" (σp "plk"), rb, hmemR atv.toNat H1, ?_, ⟨S3, H3, hl3, ?_, hid3, f2 hh⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Runs.seq (Runs.assign _ _) (Runs.seq (Runs.assign _ _) (Runs.seq hR (Runs.assign _ _)))
  · obtain ⟨t, ht⟩ := hh; exact ⟨t, by rw [f1]; exact ht⟩
  · simp [Locals.set, hr]
  · simp only [Locals.set_same]
    rw [hfr "plk" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σb, σa, Locals.set]
  · rw [Locals.set_other _ _ (by decide),
      hfr "pd" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σb, σa, Locals.set]
  · rw [Locals.set_other _ _ (by decide),
      hfr "d" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σb, σa, Locals.set]
  · rw [Locals.set_other _ _ (by decide),
      hfr "e" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σb, σa, Locals.set]
  · rw [Locals.set_other _ _ (by decide),
      hfr "w" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σb, σa, Locals.set]

/-- Writing the entry. -/
theorem setPTE_run (εR : REnv) {c : CPU} {i j : Nat} {l : RLog} {b : Region} (hcs : CSt c i j l b)
    {σ : Locals} (hlk : (σ "lk").toNat = i) (hpd : σ "pd" = b (σ "d").toNat) :
    ∃ σ' l', Runs (rprimsA εR c) setPTE σ l σ' l' ∧ CSt c i j l' (ptSet b (σ "d") (σ "e") (σ "w")) ∧
      σ' "lk" = σ "lk" ∧ σ' "pd" = σ "pd" := by
  by_cases hz : σ "pd" = 0
  · refine ⟨σ, l, Runs.ite_false (ne_false hz) Runs.skip, ?_, rfl, rfl⟩
    have : ptSet b (σ "d") (σ "e") (σ "w") = b := if_pos (by rw [← hpd]; exact hz)
    rw [this]; exact hcs
  · obtain ⟨l1, hw, hc1⟩ := cst_wr (εR := εR) hcs hlk (.bin .add (.var "pd") (.var "e")) (.var "w")
    refine ⟨σ.set "_" 0, l1, Runs.ite_true (ne_true hz) hw, ?_, by simp [Locals.set], by simp [Locals.set]⟩
    have : ptSet b (σ "d") (σ "e") (σ "w") = setCell b (b (σ "d").toNat + σ "e").toNat (σ "w") :=
      if_neg (by rw [← hpd]; exact hz)
    rw [this, ← hpd]; exact hc1

/-- **The critical section of `pt_insert` computes `ptInsertSpec`.** -/
theorem ptInsertCS_run {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    {atv : Val} (hF : ∀ tn, LockArray.FairA ε c atv.toNat tn bound) (np : Nat) (hnp : np < 2 ^ 32)
    (ndv : Val) (ne : Nat) (hne : ne < 2 ^ 32) {i : Nat} (hi : i ≠ atv.toNat) (σ : Locals) (l : RLog)
    (b : Region) (hlk : (σ "lk").toNat = i) (hcs : CSt c i atv.toNat l b) :
    ∃ σ' l' a, Runs (rprimsA εR c) (ptInsertCS atv (BitVec.ofNat 32 np) ndv (BitVec.ofNat 32 ne)) σ l σ' l' ∧
      CSt c i atv.toNat l' (ptInsertSpec np ndv ne b (pallocSpec np a).2 (σ "d") (σ "e") (σ "w")) ∧
      σ' "lk" = σ "lk" ∧ σ' "pd" = ptInsertRes np ndv ne b (pallocSpec np a).2 (σ "d") := by
  let σ0 := σ.set "pd" (b (σ "d").toNat)
  have hrd : Runs (rprimsA εR c) (.call "pd" .pull [lkE, .var "d"]) σ l σ0 l := cst_rd hcs hlk "pd" (.var "d")
  have hlk0 : σ0 "lk" = σ "lk" := by simp [σ0, Locals.set]
  have hd0 : σ0 "d" = σ "d" := by simp [σ0, Locals.set]
  have he0 : σ0 "e" = σ "e" := by simp [σ0, Locals.set]
  have hw0 : σ0 "w" = σ "w" := by simp [σ0, Locals.set]
  have hpd0 : σ0 "pd" = b (σ "d").toNat := by simp [σ0]
  by_cases hz : b (σ "d").toNat = 0
  · obtain ⟨σ1, l1, a, hpa, hc1, hr1, hlk1, hpd1, hd1, he1, hw1⟩ :=
      palloc_nested hE hRR hc hRA bound K hK hF np hnp hi (σ := σ0) hcs
    have hple := palloc_le np a
    by_cases hp : (pallocSpec np a).2 = np
    · obtain ⟨σ2, l2, hs, hc2, hlk2, hpd2⟩ := setPTE_run εR hc1 (σ := σ1) (by rw [hlk1, hlk0]; exact hlk)
        (by rw [hpd1, hpd0, hd1, hd0])
      refine ⟨σ2, l2, a, Runs.seq hrd (Runs.seq (Runs.ite_true (eq_true (hpd0.trans hz))
        (Runs.seq hpa (Runs.ite_false (ne_false (by rw [hr1, hp])) Runs.skip))) hs), ?_, ?_, ?_⟩
      · have h1 : ptSet b (σ1 "d") (σ1 "e") (σ1 "w") = b := if_pos (by rw [hd1, hd0]; exact hz)
        have h2 : ptInsertSpec np ndv ne b (pallocSpec np a).2 (σ "d") (σ "e") (σ "w") = b := by
          rw [ptInsertSpec, if_pos hz, if_pos hp]
        rw [h2]; rw [h1] at hc2; exact hc2
      · rw [hlk2, hlk1, hlk0]
      · rw [hpd2, hpd1, hpd0, ptInsertRes, if_pos hz, if_pos hp]; exact hz
    · -- a fresh page: build the table, install it, write the entry
      let x : Val := pageAddr ndv (BitVec.ofNat 32 ne) (pallocSpec np a).2
      let σ2 := σ1.set "pd" x
      let σ3 := σ2.set "k" 0
      have hg : σ1 "r" ≠ BitVec.ofNat 32 np := by
        rw [hr1]; exact ofNat_ne (by omega) hnp hp
      have ha2 : Runs (rprimsA εR c) (.assign "pd" (.bin .add (.const ndv) (.bin .mul (.var "r")
          (.const (BitVec.ofNat 32 ne))))) σ1 l1 σ2 l1 := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l1) "pd"
          (.bin .add (.const ndv) (.bin .mul (.var "r") (.const (BitVec.ofNat 32 ne))))
        have he : (Expr.bin .add (.const ndv) (.bin .mul (.var "r") (.const (BitVec.ofNat 32 ne)))).eval σ1 = x := by
          simp [Expr.eval, BinOp.eval, hr1, x, pageAddr]
        rw [he] at h; exact h
      have ha3 : Runs (rprimsA εR c) (.assign "k" (.const 0)) σ2 l1 σ3 l1 := Runs.assign _ _
      have hlk3 : (σ3 "lk").toNat = i := by
        have : σ3 "lk" = σ1 "lk" := by simp [σ3, σ2, Locals.set]
        rw [this, hlk1, hlk0]; exact hlk
      obtain ⟨σ4, l4, hz4, hc4⟩ := zero_run εR c i atv.toNat ne hne ne 0 (by omega) σ3 l1 b
        (by simp [σ3]) hlk3 hc1
      have hpd3 : σ3 "pd" = x := by simp [σ3, σ2, Locals.set]
      have f4 : ∀ z : Ident, z ≠ "_" → z ≠ "k" → σ4 z = σ3 z := fun z h1 h2 =>
        hz4.frame (by simp [frS, zeroLoop, zeroBody, Ne.symm h1, Ne.symm h2])
      have hlk4 : σ4 "lk" = σ3 "lk" := f4 _ (by decide) (by decide)
      have hpd4 : σ4 "pd" = x := (f4 _ (by decide) (by decide)).trans hpd3
      have hd4 : σ4 "d" = σ "d" := by
        rw [f4 _ (by decide) (by decide)]; simp [σ3, σ2, Locals.set, hd1, hd0]
      have he4 : σ4 "e" = σ "e" := by
        rw [f4 _ (by decide) (by decide)]; simp [σ3, σ2, Locals.set, he1, he0]
      have hw4 : σ4 "w" = σ "w" := by
        rw [f4 _ (by decide) (by decide)]; simp [σ3, σ2, Locals.set, hw1, hw0]
      obtain ⟨l5, hw5, hc5⟩ := cst_wr (εR := εR) hc4 (σ := σ4) (by rw [hlk4]; exact hlk3) (.var "d") (.var "pd")
      let σ5 := σ4.set "_" 0
      have hc5' : CSt c i atv.toNat l5 (ptNew ne b (σ "d") x) := by
        simpa [ptNew, Expr.eval, hd4, hpd4, hpd3] using hc5
      have hnewd : ptNew ne b (σ "d") x (σ "d").toNat = x := by simp [ptNew, setCell]
      obtain ⟨σ6, l6, hs, hc6, hlk6, hpd6⟩ := setPTE_run εR hc5' (σ := σ5)
        (by simp only [σ5, Locals.set_other _ _ (show ("lk" : Ident) ≠ "_" by decide)]; rw [hlk4]; exact hlk3)
        (by simp only [σ5, Locals.set_other _ _ (show ("pd" : Ident) ≠ "_" by decide),
              Locals.set_other _ _ (show ("d" : Ident) ≠ "_" by decide)]; rw [hpd4, hd4, hnewd])
      refine ⟨σ6, l6, a, Runs.seq hrd (Runs.seq (Runs.ite_true (eq_true (hpd0.trans hz))
        (Runs.seq hpa (Runs.ite_true (ne_true hg)
          (Runs.seq ha2 (Runs.seq ha3 (Runs.seq hz4 hw5)))))) hs), ?_, ?_, ?_⟩
      · have h2 : ptInsertSpec np ndv ne b (pallocSpec np a).2 (σ "d") (σ "e") (σ "w") =
            ptSet (ptNew ne b (σ "d") x) (σ "d") (σ "e") (σ "w") := by
          rw [ptInsertSpec, if_pos hz, if_neg hp]
        rw [h2]
        have h5 : σ5 "d" = σ "d" ∧ σ5 "e" = σ "e" ∧ σ5 "w" = σ "w" := by
          simp [σ5, Locals.set, hd4, he4, hw4]
        rw [h5.1, h5.2.1, h5.2.2] at hc6; exact hc6
      · rw [hlk6]; simp only [σ5, Locals.set_other _ _ (show ("lk" : Ident) ≠ "_" by decide)]
        rw [hlk4]; simp [σ3, σ2, Locals.set, hlk1, hlk0]
      · rw [hpd6]; simp only [σ5, Locals.set_other _ _ (show ("pd" : Ident) ≠ "_" by decide)]
        rw [hpd4, ptInsertRes, if_pos hz, if_neg hp]
  · obtain ⟨σ2, l2, hs, hc2, hlk2, hpd2⟩ := setPTE_run εR hcs (σ := σ0) (by rw [hlk0]; exact hlk)
      (by rw [hpd0, hd0])
    refine ⟨σ2, l2, fun _ => 0, Runs.seq hrd (Runs.seq (Runs.ite_false (eq_false (by rw [hpd0]; exact hz))
      Runs.skip) hs), ?_, by rw [hlk2, hlk0], ?_⟩
    · have h2 : ptInsertSpec np ndv ne b (pallocSpec np (fun _ => 0)).2 (σ "d") (σ "e") (σ "w") =
          ptSet b (σ "d") (σ "e") (σ "w") := by rw [ptInsertSpec, if_neg hz]
      rw [h2]; rw [hd0, he0, hw0] at hc2; exact hc2
    · rw [hpd2, hpd0, ptInsertRes, if_neg hz]

theorem ptRmvCS_run (εR : REnv) {c : CPU} {i j : Nat} {l : RLog} {b : Region} (hcs : CSt c i j l b)
    {σ : Locals} (hlk : (σ "lk").toNat = i) :
    ∃ σ' l', Runs (rprimsA εR c) ptRmvCS σ l σ' l' ∧ CSt c i j l' (ptSet b (σ "d") (σ "e") 0) ∧
      σ' "lk" = σ "lk" := by
  let σ0 := σ.set "pd" (b (σ "d").toNat)
  let σ1 := σ0.set "w" 0
  have hrd : Runs (rprimsA εR c) (.call "pd" .pull [lkE, .var "d"]) σ l σ0 l := cst_rd hcs hlk "pd" (.var "d")
  have hlk1 : σ1 "lk" = σ "lk" := by simp [σ1, σ0, Locals.set]
  obtain ⟨σ2, l2, hs, hc2, hlk2, -⟩ := setPTE_run εR hcs (σ := σ1) (by rw [hlk1]; exact hlk)
    (by simp [σ1, σ0, Locals.set])
  refine ⟨σ2, l2, Runs.seq hrd (Runs.seq (Runs.assign _ _) hs), ?_, hlk2.trans hlk1⟩
  have h : σ1 "d" = σ "d" ∧ σ1 "e" = σ "e" ∧ σ1 "w" = 0 := by simp [σ1, σ0, Locals.set]
  rw [h.1, h.2.1, h.2.2] at hc2; exact hc2

theorem ptReadCS_run (εR : REnv) {c : CPU} {i j : Nat} {l : RLog} {b : Region} (hcs : CSt c i j l b)
    {σ : Locals} (hlk : (σ "lk").toNat = i) :
    ∃ σ', Runs (rprimsA εR c) ptReadCS σ l σ' l ∧ σ' "r" = ptLookup b (σ "d") (σ "e") ∧ σ' "lk" = σ "lk" := by
  let σ0 := σ.set "pd" (b (σ "d").toNat)
  have hrd : Runs (rprimsA εR c) (.call "pd" .pull [lkE, .var "d"]) σ l σ0 l := cst_rd hcs hlk "pd" (.var "d")
  have hlk0 : σ0 "lk" = σ "lk" := by simp [σ0, Locals.set]
  have hpd0 : σ0 "pd" = b (σ "d").toNat := by simp [σ0]
  by_cases hz : b (σ "d").toNat = 0
  · refine ⟨σ0.set "r" 0, Runs.seq hrd (Runs.ite_false (ne_false (hpd0.trans hz)) (Runs.assign _ _)), ?_,
      by simp [σ0, Locals.set]⟩
    rw [ptLookup, if_pos hz]; simp
  · have h := cst_rd (εR := εR) hcs (σ := σ0) (by rw [hlk0]; exact hlk) "r" (.bin .add (.var "pd") (.var "e"))
    refine ⟨_, Runs.seq hrd (Runs.ite_true (ne_true (by rw [hpd0]; exact hz)) h), ?_, by simp [σ0, Locals.set]⟩
    rw [ptLookup, if_neg hz]; simp [Expr.eval, BinOp.eval, σ0, Locals.set]

/-! ## The guarantees -/

/-- **`pt_insert` refines `ptInsertSpec`.** Under an environment that keeps the
region log valid, and fairness of both locks, `pt_insert(d, e, w)` finishes
idle on both locks. The page table it releases is `ptInsertSpec` of the one
the previous holder released, where the page is the one `palloc` returned on
the allocation table `a` it found. -/
theorem ptInsert_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv atv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (hi : iv.toNat ≠ atv.toNat) (hidat : (S.lk atv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hFat : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    (σ : Locals) (hσ : σ "lk" = iv) (np : Nat) (hnp : np < 2 ^ 32) (ndv : Val) (ne : Nat) (hne : ne < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR) (a : Region),
      Star (rprimsA εR c) ⟨ptInsert atv (BitVec.ofNat 32 np) ndv (BitVec.ofNat 32 ne), .stop, σ, l⟩
        ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk atv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 =
        ptInsertSpec np ndv ne (hmemR iv.toNat H1) (pallocSpec np a).2 (σ "d") (σ "e") (σ "w") ∧
      σ' "pd" = ptInsertRes np ndv ne (hmemR iv.toNat H1) (pallocSpec np a).2 (σ "d") := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hidj, hfr, a, hR1, hR2⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle (j := atv.toNat) (fun h => hi h.symm) hidat bound K hK hF σ hσ
      (ptInsertCS atv (BitVec.ofNat 32 np) ndv (BitVec.ofNat 32 ne))
      (fun b σ b' σ' => ∃ a, b' = ptInsertSpec np ndv ne b (pallocSpec np a).2 (σ "d") (σ "e") (σ "w") ∧
        σ' "pd" = ptInsertRes np ndv ne b (pallocSpec np a).2 (σ "d"))
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', a, hr, hc', hlk', hpd⟩ := ptInsertCS_run hE hRR hc hRA bound K hK hFat np hnp ndv ne hne
          hi σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, a, rfl, hpd⟩)
  have hd := hfr "d" (by decide) (by decide) (by decide) (by decide)
  have he := hfr "e" (by decide) (by decide) (by decide) (by decide)
  have hw := hfr "w" (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, a, hrun, hl3, hid, hidj, ?_, ?_⟩
  · rw [hR1, hd, he, hw]
  · rw [Locals.set_other _ _ (by decide), hR2, hd]

/-- **`pt_rmv(d, e)` clears the entry**, if its table is present. -/
theorem ptRmv_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {j : Nat} (hji : j ≠ iv.toNat) (hidj : (S.lk j).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨ptRmv, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = ptSet (hmemR iv.toNat H1) (σ "d") (σ "e") 0 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, -, hfr, hR⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle hji hidj bound K hK hF σ hσ ptRmvCS
      (fun b σ b' _ => b' = ptSet b (σ "d") (σ "e") 0)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', hr, hc', hlk'⟩ := ptRmvCS_run εR hcs (σ := σ) (by rw [hlk])
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, rfl⟩)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, ?_⟩
  rw [hR, hfr "d" (by decide) (by decide) (by decide) (by decide),
    hfr "e" (by decide) (by decide) (by decide) (by decide)]

/-- **`pt_read(d, e)` returns the entry** of the page table the previous
holder released, and releases it unchanged. -/
theorem ptRead_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {j : Nat} (hji : j ≠ iv.toNat) (hidj : (S.lk j).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨ptRead, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = hmemR iv.toNat H1 ∧ σ' "r" = ptLookup (hmemR iv.toNat H1) (σ "d") (σ "e") := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, -, hfr, hR1, hR2⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle hji hidj bound K hK hF σ hσ ptReadCS
      (fun b σ b' σ' => b' = b ∧ σ' "r" = ptLookup b (σ "d") (σ "e"))
      (fun σ l b hlk hcs => by
        obtain ⟨σ', hr, hres, hlk'⟩ := ptReadCS_run εR hcs (σ := σ) (by rw [hlk])
        exact ⟨σ', l, b, hr, hcs, hlk'.trans hlk, rfl, hres⟩)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hR1, ?_⟩
  rw [Locals.set_other _ _ (by decide), hR2, hfr "d" (by decide) (by decide) (by decide) (by decide),
    hfr "e" (by decide) (by decide) (by decide) (by decide)]

/-! ## The page table is a map -/

theorem setCell_eq (b : Region) (j : Nat) (v : Val) : setCell b j v j = v := by simp [setCell]

theorem setCell_ne (b : Region) {j k : Nat} (v : Val) (h : k ≠ j) : setCell b j v k = b k := by
  simp [setCell, h]

theorem zeroFrom_zero {x : Val} : ∀ (n m : Nat) (b : Region) (k : Nat), b k = 0 → zeroFrom b x m n k = 0
  | 0, _, _, _, h => h
  | n + 1, m, b, k, h => zeroFrom_zero n (m + 1) _ k (by simp only [setCell]; split; rfl; exact h)

theorem zeroFrom_hit {x : Val} : ∀ (n m : Nat) (b : Region) (t : Nat), m ≤ t → t < m + n →
    zeroFrom b x m n (x + BitVec.ofNat 32 t).toNat = 0
  | 0, m, b, t, h1, h2 => by omega
  | n + 1, m, b, t, h1, h2 => by
    simp only [zeroFrom]
    by_cases htm : t = m
    · subst htm; exact zeroFrom_zero n _ _ _ (setCell_eq _ _ _)
    · exact zeroFrom_hit n (m + 1) _ t (by omega) (by omega)

theorem zeroFrom_miss {x : Val} : ∀ (n m : Nat) (b : Region) (k : Nat),
    (∀ t, m ≤ t → t < m + n → k ≠ (x + BitVec.ofNat 32 t).toNat) → zeroFrom b x m n k = b k
  | 0, _, _, _, _ => rfl
  | n + 1, m, b, k, h => by
    simp only [zeroFrom]
    rw [zeroFrom_miss n (m + 1) _ k (fun t h1 h2 => h t (by omega) (by omega))]
    exact setCell_ne _ _ (h m (Nat.le_refl _) (by omega))

theorem cell_lt {nd ne np p t : Nat} (hp : p < np) (ht : t < ne) : nd + p * ne + t < nd + np * ne := by
  have h : (p + 1) * ne ≤ np * ne := Nat.mul_le_mul_right ne hp
  rw [Nat.add_mul, Nat.one_mul] at h; omega

theorem cell_inj {ne p q t t' : Nat} (ht : t < ne) (ht' : t' < ne) (h : p * ne + t = q * ne + t') : p = q := by
  rcases Nat.lt_trichotomy p q with h1 | h1 | h1
  · have h2 : (p + 1) * ne ≤ q * ne := Nat.mul_le_mul_right ne h1
    rw [Nat.add_mul, Nat.one_mul] at h2; omega
  · exact h1
  · have h2 : (q + 1) * ne ≤ p * ne := Nat.mul_le_mul_right ne h1
    rw [Nat.add_mul, Nat.one_mul] at h2; omega

section Map
variable {nd ne np : Nat}

theorem addr_add (hsz : nd + np * ne < 2 ^ 32) {p : Nat} (hp : p < np) (e : Val) (he : e.toNat < ne) :
    (BitVec.ofNat 32 (nd + p * ne) + e).toNat = nd + p * ne + e.toNat := by
  have h := cell_lt (nd := nd) hp he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := nd + p * ne) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem addr_toNat (hsz : nd + np * ne < 2 ^ 32) {p : Nat} (hp : p < np) :
    (BitVec.ofNat 32 (nd + p * ne)).toNat = nd + p * ne := by
  have h : p * ne ≤ np * ne := Nat.mul_le_mul_right ne (Nat.le_of_lt hp)
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem addr_ne_zero (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) {p : Nat} (hp : p < np) :
    BitVec.ofNat 32 (nd + p * ne) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [addr_toNat hsz hp] at this
  simp at this; omega

theorem addr_inj (hne : 0 < ne) (hsz : nd + np * ne < 2 ^ 32) {p q : Nat} (hp : p < np) (hq : q < np)
    (h : BitVec.ofNat 32 (nd + p * ne) = BitVec.ofNat 32 (nd + q * ne)) : p = q := by
  have := congrArg BitVec.toNat h
  rw [addr_toNat hsz hp, addr_toNat hsz hq] at this
  exact cell_inj hne hne (by omega : p * ne + 0 = q * ne + 0)

/-- **The page-table invariant**, relating a page table `b` to the allocation
table `a`. Every present directory entry is the address of an allocated page,
and no two entries share a page. -/
structure PTInv (nd ne np : Nat) (b a : Region) : Prop where
  wf : ∀ d, d < nd → b d ≠ 0 → ∃ p, p < np ∧ b d = BitVec.ofNat 32 (nd + p * ne) ∧ a p ≠ 0
  inj : ∀ d1 d2, d1 < nd → d2 < nd → b d1 ≠ 0 → b d1 = b d2 → d1 = d2

/-- What an update of entry `(d, e)` through the table on page `p` looks like:
`b'` is the page table after, `A'` the allocation table after. -/
structure Shape (nd ne : Nat) (b b' A' a : Region) (d e v : Val) (p : Nat) : Prop where
  pde : b' d.toNat = BitVec.ofNat 32 (nd + p * ne)
  old : b d.toNat ≠ 0 → b d.toNat = BitVec.ofNat 32 (nd + p * ne)
  dir : ∀ d', d' < nd → d' ≠ d.toNat → b' d' = b d'
  hit : b' (nd + p * ne + e.toNat) = v
  out : ∀ k, nd ≤ k → (∀ t, t < ne → k ≠ nd + p * ne + t) → b' k = b k
  tbl : ∀ t, t < ne → t ≠ e.toNat → b' (nd + p * ne + t) = if b d.toNat = 0 then 0 else b (nd + p * ne + t)
  uniq : ∀ d', d' < nd → d' ≠ d.toNat → b d' ≠ BitVec.ofNat 32 (nd + p * ne)
  used : A' p ≠ 0
  mono : ∀ q, a q ≠ 0 → A' q ≠ 0

/-- Writing an entry whose table is present. -/
theorem shape_old (hsz : nd + np * ne < 2 ^ 32) {b a : Region} (hI : PTInv nd ne np b a) (d e v : Val)
    (hd : d.toNat < nd) (he : e.toNat < ne) (hz : b d.toNat ≠ 0) :
    ∃ p, p < np ∧ Shape nd ne b (ptSet b d e v) a a d e v p := by
  obtain ⟨p, hp, hbp, hap⟩ := hI.wf d.toNat hd hz
  have hb' : ptSet b d e v = setCell b (nd + p * ne + e.toNat) v := by
    rw [ptSet, if_neg hz, hbp, addr_add hsz hp e he]
  rw [hb']
  refine ⟨p, hp, ⟨?_, fun _ => hbp, ?_, setCell_eq _ _ _, ?_, ?_, ?_, hap, fun _ h => h⟩⟩
  · rw [setCell_ne _ _ (by omega)]; exact hbp
  · intro d' hd' _; exact setCell_ne _ _ (by omega)
  · intro k _ hout; exact setCell_ne _ _ (hout _ he)
  · intro t _ hte; rw [setCell_ne _ _ (by omega), if_neg hz]
  · intro d' hd' hne h
    exact hne (hI.inj d.toNat d' hd hd' hz (hbp.trans h.symm)).symm

/-- Installing a fresh page `p` as the table, then writing the entry. -/
theorem shape_new (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) {b a A' : Region} (hI : PTInv nd ne np b a)
    (d e v : Val) (hd : d.toNat < nd) (he : e.toNat < ne) (hz : b d.toNat = 0) {p : Nat} (hp : p < np)
    (hfree : a p = 0) (hA1 : A' p ≠ 0) (hA2 : ∀ q, a q ≠ 0 → A' q ≠ 0) :
    Shape nd ne b (ptSet (ptNew ne b d (pageAddr (BitVec.ofNat 32 nd) (BitVec.ofNat 32 ne) p)) d e v)
      A' a d e v p := by
  have hX : pageAddr (BitVec.ofNat 32 nd) (BitVec.ofNat 32 ne) p = BitVec.ofNat 32 (nd + p * ne) := by
    simp [pageAddr, BitVec.ofNat_add, BitVec.ofNat_mul]
  have hX0 := addr_ne_zero hnd hsz hp
  have hoff : ∀ t, t < ne → (BitVec.ofNat 32 (nd + p * ne) + BitVec.ofNat 32 t).toNat = nd + p * ne + t := by
    intro t ht
    have h := cell_lt (nd := nd) hp ht
    have ht' : (BitVec.ofNat 32 t).toNat = t := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have := addr_add hsz hp (BitVec.ofNat 32 t) (by rw [ht']; exact ht)
    rw [ht'] at this; exact this
  have hZhit : ∀ t, t < ne → zeroFrom b (BitVec.ofNat 32 (nd + p * ne)) 0 ne (nd + p * ne + t) = 0 := by
    intro t ht
    have := zeroFrom_hit (x := BitVec.ofNat 32 (nd + p * ne)) ne 0 b t (Nat.zero_le _) (by omega)
    rwa [hoff t ht] at this
  have hZmiss : ∀ k, (∀ t, t < ne → k ≠ nd + p * ne + t) →
      zeroFrom b (BitVec.ofNat 32 (nd + p * ne)) 0 ne k = b k := fun k hk =>
    zeroFrom_miss ne 0 b k (fun t _ ht => by rw [hoff t (by omega)]; exact hk t (by omega))
  have hnewd : ptNew ne b d (BitVec.ofNat 32 (nd + p * ne)) d.toNat = BitVec.ofNat 32 (nd + p * ne) :=
    setCell_eq _ _ _
  have hb' : ptSet (ptNew ne b d (BitVec.ofNat 32 (nd + p * ne))) d e v =
      setCell (setCell (zeroFrom b (BitVec.ofNat 32 (nd + p * ne)) 0 ne) d.toNat
        (BitVec.ofNat 32 (nd + p * ne))) (nd + p * ne + e.toNat) v := by
    rw [ptSet, if_neg (by rw [hnewd]; exact hX0), hnewd, addr_add hsz hp e he]; rfl
  rw [hX, hb']
  refine ⟨?_, fun h => absurd hz h, ?_, setCell_eq _ _ _, ?_, ?_, ?_, hA1, hA2⟩
  · rw [setCell_ne _ _ (by omega)]; exact setCell_eq _ _ _
  · intro d' hd' hne
    rw [setCell_ne _ _ (by omega), setCell_ne _ _ hne]; exact hZmiss d' (fun t _ => by omega)
  · intro k hk hout
    rw [setCell_ne _ _ (hout _ he), setCell_ne _ _ (by omega)]; exact hZmiss k hout
  · intro t ht hte
    rw [setCell_ne _ _ (by omega), setCell_ne _ _ (by omega), hZhit t ht, if_pos hz]
  · intro d' hd' _ h
    obtain ⟨q, hq, hbq, haq⟩ := hI.wf d' hd' (by rw [h]; exact hX0)
    rw [h] at hbq
    have hpq := addr_inj (by omega) hsz hp hq hbq
    subst hpq; exact haq hfree

/-- The entry just written reads back. -/
theorem Shape.lookup_same {b b' A' a : Region} {d e v : Val} {p : Nat} (hS : Shape nd ne b b' A' a d e v p)
    (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) (hp : p < np) (he : e.toNat < ne) : ptLookup b' d e = v := by
  rw [ptLookup, if_neg (by rw [hS.pde]; exact addr_ne_zero hnd hsz hp), hS.pde, addr_add hsz hp e he]
  exact hS.hit

/-- Every other entry reads as before. -/
theorem Shape.lookup_other {b b' A' a : Region} {d e v : Val} {p : Nat} (hS : Shape nd ne b b' A' a d e v p)
    (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) (hp : p < np) (hI : PTInv nd ne np b a) {d' e' : Val}
    (hd' : d'.toNat < nd) (he' : e'.toNat < ne) (hne : ¬ (d' = d ∧ e' = e)) :
    ptLookup b' d' e' = ptLookup b d' e' := by
  by_cases hdd : d'.toNat = d.toNat
  · have hd : d' = d := BitVec.eq_of_toNat_eq hdd
    subst hd
    have hee : e'.toNat ≠ e.toNat := fun h => hne ⟨rfl, BitVec.eq_of_toNat_eq h⟩
    rw [ptLookup, if_neg (by rw [hS.pde]; exact addr_ne_zero hnd hsz hp), hS.pde, addr_add hsz hp e' he',
      hS.tbl _ he' hee, ptLookup]
    by_cases hz : b d'.toNat = 0
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz, hS.old hz, addr_add hsz hp e' he']
  · rw [ptLookup, ptLookup, hS.dir _ hd' hdd]
    by_cases hz : b d'.toNat = 0
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz]
      obtain ⟨q, hq, hbq, -⟩ := hI.wf _ hd' hz
      rw [hbq, addr_add hsz hq e' he']
      refine hS.out _ (by omega) (fun t ht heq => ?_)
      have hqp : q = p := cell_inj he' ht (by omega)
      subst hqp
      exact hS.uniq _ hd' hdd hbq

/-- The invariant holds again, with the allocation table after. -/
theorem Shape.inv {b b' A' a : Region} {d e v : Val} {p : Nat} (hS : Shape nd ne b b' A' a d e v p)
    (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) (hp : p < np) (hd : d.toNat < nd)
    (hI : PTInv nd ne np b a) : PTInv nd ne np b' A' := by
  constructor
  · intro d' hd' hz'
    by_cases hdd : d' = d.toNat
    · subst hdd; exact ⟨p, hp, hS.pde, hS.used⟩
    · rw [hS.dir _ hd' hdd] at hz' ⊢
      obtain ⟨q, hq, hbq, haq⟩ := hI.wf _ hd' hz'
      exact ⟨q, hq, hbq, hS.mono q haq⟩
  · intro d1 d2 h1 h2 hz heq
    by_cases e1 : d1 = d.toNat
    · by_cases e2 : d2 = d.toNat
      · rw [e1, e2]
      · subst e1; rw [hS.pde, hS.dir _ h2 e2] at heq
        exact absurd heq.symm (hS.uniq _ h2 e2)
    · by_cases e2 : d2 = d.toNat
      · subst e2; rw [hS.pde, hS.dir _ h1 e1] at heq
        exact absurd heq (hS.uniq _ h1 e1)
      · rw [hS.dir _ h1 e1] at hz heq; rw [hS.dir _ h2 e2] at heq
        exact hI.inj d1 d2 h1 h2 hz heq

/-- `pt_insert` either fails and changes nothing, or updates the entry through
some page's table. -/
theorem insert_shape (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) {b a : Region} (hI : PTInv nd ne np b a)
    (d e v : Val) (hd : d.toNat < nd) (he : e.toNat < ne) :
    (b d.toNat = 0 ∧ ptInsertSpec np (BitVec.ofNat 32 nd) ne b (pallocSpec np a).2 d e v = b ∧
        (pallocSpec np a).1 = a) ∨
    ∃ p, p < np ∧ Shape nd ne b (ptInsertSpec np (BitVec.ofNat 32 nd) ne b (pallocSpec np a).2 d e v)
      (if b d.toNat = 0 then (pallocSpec np a).1 else a) a d e v p := by
  obtain ⟨hf1, hf2⟩ := palloc_fresh np a
  by_cases hz : b d.toNat = 0
  · by_cases hp : (pallocSpec np a).2 = np
    · left
      exact ⟨hz, by rw [ptInsertSpec, if_pos hz, if_pos hp], (hf2 (by rw [hp]; exact Nat.lt_irrefl _)).1⟩
    · right
      have hlt : (pallocSpec np a).2 < np := Nat.lt_of_le_of_ne (palloc_le np a) hp
      obtain ⟨hfree, hset, hoth, -⟩ := hf1 hlt
      refine ⟨_, hlt, ?_⟩
      rw [ptInsertSpec, if_pos hz, if_neg hp, if_pos hz]
      refine shape_new hnd hsz hI d e v hd he hz hlt hfree (by rw [hset]; decide) (fun q hq => ?_)
      by_cases hqp : q = (pallocSpec np a).2
      · rw [hqp] at hq; exact absurd hfree hq
      · rw [hoth q hqp]; exact hq
  · right
    obtain ⟨p, hp, hS⟩ := shape_old hsz hI d e v hd he hz
    exact ⟨p, hp, by rw [ptInsertSpec, if_neg hz, if_neg hz]; exact hS⟩

/-- **After a successful insert, the new entry reads back.** -/
theorem insert_lookup_same (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) {b a : Region}
    (hI : PTInv nd ne np b a) (d e v : Val) (hd : d.toNat < nd) (he : e.toNat < ne)
    (hok : ptInsertSpec np (BitVec.ofNat 32 nd) ne b (pallocSpec np a).2 d e v d.toNat ≠ 0) :
    ptLookup (ptInsertSpec np (BitVec.ofNat 32 nd) ne b (pallocSpec np a).2 d e v) d e = v := by
  rcases insert_shape hnd hsz hI d e v hd he with ⟨hz, hb, -⟩ | ⟨p, hp, hS⟩
  · rw [hb] at hok; exact absurd hz hok
  · exact hS.lookup_same hnd hsz hp he

/-- **An insert leaves every other entry as it was.** -/
theorem insert_lookup_other (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) {b a : Region}
    (hI : PTInv nd ne np b a) (d e v : Val) (hd : d.toNat < nd) (he : e.toNat < ne) {d' e' : Val}
    (hd' : d'.toNat < nd) (he' : e'.toNat < ne) (hne : ¬ (d' = d ∧ e' = e)) :
    ptLookup (ptInsertSpec np (BitVec.ofNat 32 nd) ne b (pallocSpec np a).2 d e v) d' e' = ptLookup b d' e' := by
  rcases insert_shape hnd hsz hI d e v hd he with ⟨-, hb, -⟩ | ⟨p, hp, hS⟩
  · rw [hb]
  · exact hS.lookup_other hnd hsz hp hI hd' he' hne

/-- **An insert keeps the invariant**, with the allocation table `palloc`
leaves if it was called. -/
theorem insert_inv (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) {b a : Region}
    (hI : PTInv nd ne np b a) (d e v : Val) (hd : d.toNat < nd) (he : e.toNat < ne) :
    PTInv nd ne np (ptInsertSpec np (BitVec.ofNat 32 nd) ne b (pallocSpec np a).2 d e v)
      (if b d.toNat = 0 then (pallocSpec np a).1 else a) := by
  rcases insert_shape hnd hsz hI d e v hd he with ⟨hz, hb, ha⟩ | ⟨p, hp, hS⟩
  · rw [hb, if_pos hz, ha]; exact hI
  · exact hS.inv hnd hsz hp hd hI

/-- **Unmapping clears the entry and leaves every other entry as it was.** -/
theorem rmv_lookup (hnd : 0 < nd) (hsz : nd + np * ne < 2 ^ 32) {b a : Region} (hI : PTInv nd ne np b a)
    (d e : Val) (hd : d.toNat < nd) (he : e.toNat < ne) :
    ptLookup (ptSet b d e 0) d e = 0 ∧
    (∀ d' e' : Val, d'.toNat < nd → e'.toNat < ne → ¬ (d' = d ∧ e' = e) →
      ptLookup (ptSet b d e 0) d' e' = ptLookup b d' e') ∧
    PTInv nd ne np (ptSet b d e 0) a := by
  by_cases hz : b d.toNat = 0
  · have hb : ptSet b d e 0 = b := if_pos hz
    rw [hb]; exact ⟨by rw [ptLookup, if_pos hz], fun _ _ _ _ _ => rfl, hI⟩
  · obtain ⟨p, hp, hS⟩ := shape_old hsz hI d e 0 hd he hz
    exact ⟨hS.lookup_same hnd hsz hp he, fun d' e' hd' he' hne => hS.lookup_other hnd hsz hp hI hd' he' hne,
      hS.inv hnd hsz hp hd hI⟩

end Map

end KernPT
