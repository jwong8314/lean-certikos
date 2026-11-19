import CertiKOS.MPTNew

/-!
# mCertiKOS `pt_resv2`: one page mapped in two address spaces, ported

`pt_resv2` allocates a page from the first process's quota and maps it in
both processes. Shared memory is built on it.

Ported from `objects/ObjLMM0.v`: `ptResv2_spec`, here over the count-based
`ptInsert_spec` as `ptResv_spec` is. Ported from `mm/MPTInitCSource.v`: the C
code. (The C comment in the sources tests `result == MagicNumber` before the
second `pt_insert`; the Clight code they verify tests `!=`, which is what the
specification says and what is ported here.)

* `ptInsert_keeps`: **`ptInsert_spec` preserves the allocation-table
  invariant**, keeps every container within its quota, and returns at most
  `MagicNumber`. `pt_resv2` needs it between its two calls of `pt_insert`.
* `ptResv2_triple`: **the C code refines `ptResv2_spec`.** It writes only the
  allocation table, the containers and the page tables (cells below
  `cb + 5 * num_id` or from `pb` on), so data placed between them is kept.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MPTNew

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern

/-! ## `pt_insert`'s specification keeps the invariants -/

/-- Every container is within its quota. -/
def UQ (ac : ContainerPool) : Prop := ∀ i, (ac i).cusage ≤ (ac i).cquota

theorem alloc_usage {d d' : RData} {id b : Nat} (hu : UQ d.AC)
    (h : container_alloc_spec id d = some (d', b)) : UQ d'.AC := by
  unfold container_alloc_spec at h
  simp only at h
  by_cases hiu : d.init = true ∧ (d.AC id).cused = true
  · rw [if_pos hiu] at h
    by_cases hlt : (d.AC id).cusage < (d.AC id).cquota
    · rw [if_pos hlt] at h
      cases hff : first_free d.AT d.nps with
      | none => rw [hff] at h; cases h
      | some p =>
        rw [hff] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        intro i
        by_cases e : i = id
        · subst e; simp only [setAt_eq]; omega
        · simp only [setAt_ne _ _ e]; exact hu i
    · rw [if_neg hlt] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hu
  · rw [if_neg hiu] at h; cases h

/-- Marking a free page allocated, with any permission but `PGUndef`, keeps
the allocation-table invariant. -/
theorem at_alloc_inv {maxpage kl kh : Nat} {d : PData} (hI : ATInv maxpage kl kh d) {pi : Nat}
    (hff : first_free d.AT d.nps = some pi) {x : PPgInfo} (hx : x ≠ .PGUndef) :
    ATInv maxpage kl kh { d with AT := setAt d.AT pi (.ATValid true .ATNorm 0), pperm := setAt d.pperm pi x } := by
  obtain ⟨hi0, hin', ⟨c, hc⟩, -⟩ := first_free_some hff
  refine ⟨hI.valid_nps, fun j hj => ?_, fun j h1 h2 => ?_, fun j hj => ?_⟩
  · by_cases hji : j = pi
    · subst hji; have := hI.valid_AT_kern j hj; rw [hc] at this; cases this
    · simp only [setAt_ne _ _ hji]; exact hI.valid_AT_kern j hj
  · by_cases hji : j = pi
    · subst hji; simp only [setAt_eq]; exact ⟨true, Or.inl ⟨0, rfl⟩⟩
    · simp only [setAt_ne _ _ hji]; exact hI.valid_AT_usr j h1 h2
  · by_cases hji : j = pi
    · subst hji; simp only [setAt_eq]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ _ => hx⟩
    · simp only [setAt_ne _ _ hji]; exact hI.valid_pperm j hj

theorem allocPDE_keeps {maxpage kl kh num_proc nn vadr : Nat} {d d2 : PTData} {v : Nat}
    (hI : ATInv maxpage kl kh d.toPData) (h : ptAllocPDE_spec num_proc nn vadr d = some (d2, v)) :
    ATInv maxpage kl kh d2.toPData ∧ (UQ d.AC → UQ d2.AC) := by
  unfold ptAllocPDE_spec at h
  simp only at h
  by_cases hc : d.init = true ∧ d.ipt = true ∧ (d.AC nn).cused = true ∧ pt_Arg' num_proc nn vadr
  · rw [if_pos hc] at h
    by_cases hPT : nn = d.PT
    · rw [if_pos hPT] at h; cases h
    · rw [if_neg hPT] at h
      cases hp : d.ptpool nn (PDX vadr) with
      | PDEValid pi pdt => rw [hp] at h; cases h
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
      | PDEUnPresent =>
        rw [hp] at h; simp only at h
        by_cases hlt : (d.AC nn).cusage < (d.AC nn).cquota
        · rw [if_pos hlt] at h
          cases hff : first_free d.AT d.nps with
          | none => rw [hff] at h; cases h
          | some p =>
            rw [hff] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
            refine ⟨at_alloc_inv hI hff (x := .PGHide nn (PDX vadr)) (fun e => by cases e), fun hu i => ?_⟩
            by_cases e : i = nn
            · subst e; simp only [setAt_eq]; omega
            · simp only [setAt_ne _ _ e]; exact hu i
        · rw [if_neg hlt] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact ⟨hI, fun hu => hu⟩
  · rw [if_neg hc] at h; cases h

theorem insertPTE_keeps {maxpage kl kh nn vadr padr : Nat} {p : PTPerm} {d d' : PTData}
    (hI : ATInv maxpage kl kh d.toPData) (h : ptInsertPTE_spec nn vadr padr p d = some d') :
    ATInv maxpage kl kh d'.toPData ∧ d'.AC = d.AC := by
  unfold ptInsertPTE_spec at h
  by_cases hin : d.init = true
  · rw [if_pos hin] at h
    by_cases hPT : nn = d.PT
    · rw [if_pos hPT] at h; cases h
    · rw [if_neg hPT] at h
      cases hp : d.ptpool nn (PDX vadr) with
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
      | PDEUnPresent => rw [hp] at h; cases h
      | PDEValid pi pdt =>
        rw [hp] at h; simp only at h
        by_cases hpi : 0 < pi ∧ pi < 2 ^ 32 - 1
        · rw [if_pos hpi] at h
          cases hA : d.AT padr with
          | ATUndef => rw [hA] at h; cases h
          | ATValid b0 t c0 =>
            rw [hA] at h
            cases b0 with
            | false => cases h
            | true =>
              cases t with
              | ATKern => cases h
              | ATResv => cases h
              | ATNorm =>
                simp only at h
                by_cases hc : c0 < 2 ^ 32 - 1
                · rw [if_pos hc] at h
                  simp only [Option.some.injEq] at h; subst h
                  refine ⟨⟨hI.valid_nps, fun j hj => ?_, fun j h1 h2 => ?_, fun j hj => ?_⟩, rfl⟩
                  · by_cases hji : j = padr
                    · subst hji; have := hI.valid_AT_kern j hj; rw [hA] at this; cases this
                    · simp only [setAt_ne _ _ hji]; exact hI.valid_AT_kern j hj
                  · by_cases hji : j = padr
                    · subst hji; simp only [setAt_eq]; exact ⟨true, Or.inl ⟨c0 + 1, rfl⟩⟩
                    · simp only [setAt_ne _ _ hji]; exact hI.valid_AT_usr j h1 h2
                  · by_cases hji : j = padr
                    · subst hji; simp only [setAt_eq]
                      exact ⟨fun _ => ⟨c0 + 1, rfl⟩, fun _ _ => (hI.valid_pperm j hj).2 c0 hA⟩
                    · simp only [setAt_ne _ _ hji]; exact hI.valid_pperm j hj
                · rw [if_neg hc] at h; cases h
        · rw [if_neg hpi] at h; cases h
  · rw [if_neg hin] at h; cases h

/-- **`ptInsert_spec` keeps the invariants.** -/
theorem ptInsert_keeps {maxpage kl kh num_proc nn vadr padr perm : Nat} {d d' : PTData} {r : Nat}
    (hI : ATInv maxpage kl kh d.toPData)
    (h : ptInsert_spec maxpage num_proc nn vadr padr perm d = some (d', r)) :
    ATInv maxpage kl kh d'.toPData ∧ (UQ d.AC → UQ d'.AC) ∧ r ≤ maxpage + 1 := by
  unfold ptInsert_spec at h
  by_cases hc : d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg num_proc nn vadr padr d.nps
  · rw [if_pos hc] at h
    cases hz : ZtoPerm perm with
    | none => rw [hz] at h; cases h
    | some p =>
      rw [hz] at h; simp only at h
      cases hp : d.ptpool nn (PDX vadr) with
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
      | PDEValid pi pdt =>
        rw [hp] at h; simp only at h
        cases hi : ptInsertPTE_spec nn vadr padr p d with
        | none => rw [hi] at h; cases h
        | some d1 =>
          rw [hi] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := insertPTE_keeps hI hi
          exact ⟨h1, fun hu => by rw [h2]; exact hu, Nat.zero_le _⟩
      | PDEUnPresent =>
        rw [hp] at h; simp only at h
        cases ha : ptAllocPDE_spec num_proc nn vadr d with
        | none => rw [ha] at h; cases h
        | some pr =>
          obtain ⟨d2, v⟩ := pr
          rw [ha] at h; simp only at h
          obtain ⟨hI2, hu2⟩ := allocPDE_keeps hI ha
          obtain ⟨hnps, -, hv⟩ := allocPDE_facts ha
          by_cases hv0 : v = 0
          · rw [if_pos hv0] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨hI2, hu2, Nat.le_refl _⟩
          · rw [if_neg hv0] at h
            cases hi : ptInsertPTE_spec nn vadr padr p d2 with
            | none => rw [hi] at h; cases h
            | some d3 =>
              rw [hi] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              obtain ⟨h1, h2⟩ := insertPTE_keeps hI2 hi
              have := hI.valid_nps.2
              exact ⟨h1, fun hu => by rw [h2]; exact hu2 hu, by rcases hv with h0 | ⟨-, h3⟩ <;> omega⟩
  · rw [if_neg hc] at h; cases h

/-! ## `pt_insert`'s specification keeps the paging flags -/

theorem insertPTE_flags {nn vadr padr : Nat} {p : PTPerm} {d d' : PTData}
    (h : ptInsertPTE_spec nn vadr padr p d = some d') : d'.pg = d.pg ∧ d'.ipt = d.ipt := by
  unfold ptInsertPTE_spec at h
  repeat' (split at h)
  all_goals first
    | (cases h; exact ⟨rfl, rfl⟩)
    | cases h

theorem allocPDE_flags {num_proc nn vadr : Nat} {d d' : PTData} {v : Nat}
    (h : ptAllocPDE_spec num_proc nn vadr d = some (d', v)) : d'.pg = d.pg ∧ d'.ipt = d.ipt := by
  unfold ptAllocPDE_spec at h
  simp only at h
  repeat' (split at h)
  all_goals first
    | (cases h; exact ⟨rfl, rfl⟩)
    | cases h

theorem ptInsert_flags {maxpage num_proc nn vadr padr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptInsert_spec maxpage num_proc nn vadr padr perm d = some (d', r)) :
    d'.pg = d.pg ∧ d'.ipt = d.ipt := by
  unfold ptInsert_spec at h
  by_cases hc : d.init = true ∧ d.ipt = true ∧ d.pg = true ∧ pt_Arg num_proc nn vadr padr d.nps
  · rw [if_pos hc] at h
    cases hz : ZtoPerm perm with
    | none => rw [hz] at h; cases h
    | some p =>
      rw [hz] at h; simp only at h
      cases hp : d.ptpool nn (PDX vadr) with
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
      | PDEValid pi pdt =>
        rw [hp] at h; simp only at h
        cases hi : ptInsertPTE_spec nn vadr padr p d with
        | none => rw [hi] at h; cases h
        | some d1 =>
          rw [hi] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact insertPTE_flags hi
      | PDEUnPresent =>
        rw [hp] at h; simp only at h
        cases ha : ptAllocPDE_spec num_proc nn vadr d with
        | none => rw [ha] at h; cases h
        | some pr =>
          obtain ⟨d2, v⟩ := pr
          rw [ha] at h; simp only at h
          obtain ⟨f1, f2⟩ := allocPDE_flags ha
          by_cases hv0 : v = 0
          · rw [if_pos hv0] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
            exact ⟨f1, f2⟩
          · rw [if_neg hv0] at h
            cases hi : ptInsertPTE_spec nn vadr padr p d2 with
            | none => rw [hi] at h; cases h
            | some d3 =>
              rw [hi] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
              obtain ⟨g1, g2⟩ := insertPTE_flags hi
              exact ⟨g1.trans f1, g2.trans f2⟩
  · rw [if_neg hc] at h; cases h

/-! ## `pt_resv2` -/

/-- **`ptResv2_spec`**: allocate a page from process `n`'s quota, map it at
`vadr` in `n` and at `vadr'` in `n'`. Returns `MagicNumber` if a page or a
second-level table could not be allocated. -/
def ptResv2_spec (maxpage num_proc : Nat) (n vadr perm n' vadr' perm' : Nat) (d : PTData) :
    Option (PTData × Nat) :=
  match container_alloc_spec n d.toRData with
  | some (r1, b) =>
    if b = 0 then some (d, maxpage + 1)
    else
      match ptInsert_spec maxpage num_proc n vadr b perm { d with toRData := r1 } with
      | some (d2, v) =>
        if v = maxpage + 1 then some (d2, maxpage + 1)
        else ptInsert_spec maxpage num_proc n' vadr' b perm' d2
      | none => none
  | none => none

/-- **`ptResv2_spec` keeps the invariants**, and returns at most `MagicNumber`. -/
theorem ptResv2_keeps {maxpage kl kh num_proc n vadr perm n' vadr' perm' : Nat} {d d' : PTData} {r : Nat}
    (hI : ATInv maxpage kl kh d.toPData)
    (h : ptResv2_spec maxpage num_proc n vadr perm n' vadr' perm' d = some (d', r)) :
    ATInv maxpage kl kh d'.toPData ∧ (UQ d.AC → UQ d'.AC) ∧ r ≤ maxpage + 1 := by
  unfold ptResv2_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h; simp only at h
    by_cases hb : b = 0
    · rw [if_pos hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hI, fun hu => hu, Nat.le_refl _⟩
    · rw [if_neg hb] at h
      have hI1 : ATInv maxpage kl kh ({ d with toRData := r1 } : PTData).toPData := alloc_at_inv hI hA
      cases h1 : ptInsert_spec maxpage num_proc n vadr b perm { d with toRData := r1 } with
      | none => rw [h1] at h; cases h
      | some pr2 =>
        obtain ⟨d2, v⟩ := pr2
        rw [h1] at h; simp only at h
        obtain ⟨hI2, hu2, hv⟩ := ptInsert_keeps hI1 h1
        have hu1 : UQ d.AC → UQ d2.AC := fun hu => hu2 (alloc_usage hu hA)
        by_cases hvm : v = maxpage + 1
        · rw [if_pos hvm] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨hI2, hu1, Nat.le_refl _⟩
        · rw [if_neg hvm] at h
          obtain ⟨hI3, hu3, hr⟩ := ptInsert_keeps hI2 h
          exact ⟨hI3, fun hu => hu3 (hu1 hu), hr⟩

/-- **`ptResv2_spec` keeps the paging flags.** -/
theorem ptResv2_flags {maxpage num_proc n vadr perm n' vadr' perm' : Nat} {d d' : PTData} {r : Nat}
    (h : ptResv2_spec maxpage num_proc n vadr perm n' vadr' perm' d = some (d', r)) :
    d'.pg = d.pg ∧ d'.ipt = d.ipt := by
  unfold ptResv2_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h; simp only at h
    by_cases hb : b = 0
    · rw [if_pos hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, rfl⟩
    · rw [if_neg hb] at h
      cases h1 : ptInsert_spec maxpage num_proc n vadr b perm { d with toRData := r1 } with
      | none => rw [h1] at h; cases h
      | some pr2 =>
        obtain ⟨d2, v⟩ := pr2
        rw [h1] at h; simp only at h
        obtain ⟨f1, f2⟩ := ptInsert_flags h1
        by_cases hvm : v = maxpage + 1
        · rw [if_pos hvm] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact ⟨f1, f2⟩
        · rw [if_neg hvm] at h
          obtain ⟨g1, g2⟩ := ptInsert_flags h
          exact ⟨g1.trans f1, g2.trans f2⟩

/-- ```
pi = container_alloc(proc_index);
if (pi == 0) result = MagicNumber;
else {
  result = pt_insert(proc_index, vaddr, pi, perm);
  if (result != MagicNumber) result = pt_insert(proc_index2, vaddr2, pi, perm2);
}
return result;
```
The second call's arguments are passed by `n = n2; vaddr = vaddr2; perm = perm2`. -/
def ptResv2S (cb maxpage pb fb : Nat) : Stmt APrim :=
  .seq (.assign "id" (.var "n")) (.seq (ctAllocCS cb maxpage) (.seq (.assign "padr" (.var "r"))
    (.ite (.bin .eq (.var "padr") (.const 0)) (.assign "r" (.const (BitVec.ofNat 32 (maxpage + 1))))
      (.seq (ptInsertS cb maxpage pb fb)
        (.ite (.bin .ne (.var "r") (.const (BitVec.ofNat 32 (maxpage + 1))))
          (.seq (.assign "n" (.var "n2")) (.seq (.assign "vaddr" (.var "vaddr2"))
            (.seq (.assign "perm" (.var "perm2")) (ptInsertS cb maxpage pb fb))))
          .skip)))))

section Resv2
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **`pt_resv2` refines `ptResv2_spec`.** -/
theorem ptResv2_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (nn vadr perm nn' vadr' perm' : Nat) (hnid : nn < num_id) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => k < cb + 5 * num_id ∨ pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        σ "perm" = BitVec.ofNat 32 perm ∧ σ "n2" = BitVec.ofNat 32 nn' ∧
        σ "vaddr2" = BitVec.ofNat 32 vadr' ∧ σ "perm2" = BitVec.ofNat 32 perm' ∧
        ATInv maxpage kl kh d.toPData ∧ UQ d.AC ∧
        ∃ d1 r, ptResv2_spec maxpage num_proc nn vadr perm nn' vadr' perm' d = some (d1, r))
      (ptResv2S cb maxpage pb fb)
      (fun _ d σ' d' => ∃ r, ptResv2_spec maxpage num_proc nn vadr perm nn' vadr' perm' d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hn, hva, hpe, hn2, hva2, hpe2, hI, hu, dF, rF, hs⟩
  have hs0 := hs
  have hmagic : maxpage + 1 < 2 ^ 32 := by omega
  unfold ptResv2_spec at hs
  cases hA : container_alloc_spec nn d.toRData with
  | none => rw [hA] at hs; cases hs
  | some pr =>
    obtain ⟨r1, bq⟩ := pr
    rw [hA] at hs; simp only at hs
    let σa := σ.set "id" (BitVec.ofNat 32 nn)
    have ha0 : Runs (rprimsA εR c) (.assign "id" (.var "n")) σ l σa l := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σ) (l := l) "id" (.var "n")
      have e : (Expr.var "n").eval σ = BitVec.ofNat 32 nn := hn
      rw [e] at h; exact h
    obtain ⟨σb, lb, bb, db, hrb, hcsb, hMb, hlkb, hfb, r1', hdb, r, hsr, hrr⟩ :=
      container_alloc_lift εR c i0 hL hmax hnum (kl := kl) (kh := kh) nn hnid σa l b d
        (by simpa [σa, Locals.set] using hlk) hcs hM ⟨by simp [σa], hI, hu nn, _, _, hA⟩
    rw [hA] at hsr
    simp only [Option.some.injEq, Prod.mk.injEq] at hsr; obtain ⟨hr1, hrb'⟩ := hsr
    rw [← hr1] at hdb; rw [← hrb'] at hrr
    have frb : ∀ z : Ident, z = "n" ∨ z = "vaddr" ∨ z = "perm" ∨ z = "n2" ∨ z = "vaddr2" ∨ z = "perm2" →
        σb z = σ z := by
      intro z hz
      have h1 : σb z = σa z := by
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact hrb.frame (by simp [frS, ctAllocCS, pallocCS, getNpsS, pallocLoop, loopBody, isNormS, atGetS,
            atSetS, atSetCS])
      rw [h1]
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [σa, Locals.set]
    let σc := σb.set "padr" (BitVec.ofNat 32 bq)
    have hac : Runs (rprimsA εR c) (.assign "padr" (.var "r")) σb lb σc lb := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σb) (l := lb) "padr" (.var "r")
      have e : (Expr.var "r").eval σb = BitVec.ofNat 32 bq := hrr
      rw [e] at h; exact h
    have hlkc : (σc "lk").toNat = i0 := by simp [σc, Locals.set, hlkb, σa, hlk]
    rcases alloc_facts (hu nn) hA with ⟨hb0, hr1d⟩ | ⟨hbpos, hblt, hu2⟩
    · rw [if_pos hb0] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
      have hdbd : db = d := by rw [hdb, hr1d]
      rw [hdbd] at hMb
      refine ⟨_, lb, bb, d, Runs.seq ha0 (Runs.seq hrb (Runs.seq hac (Runs.ite_true
        (eq_true (by simp [σc, hb0])) (Runs.assign _ _)))), hcsb, hMb, ?_,
        fun k hk => hfb k (fun h => hk (Or.inl h)), maxpage + 1, by rw [hs0, hdF, hrF], by simp [Expr.eval]⟩
      rw [Locals.set_other _ _ (by decide)]; simp [σc, Locals.set, hlkb, σa]
    · rw [if_neg (by omega)] at hs
      have hnpsm : d.nps ≤ maxpage := hI.valid_nps.2
      have hne : σc "padr" ≠ 0 := by
        have h : (BitVec.ofNat 32 bq : Val) ≠ BitVec.ofNat 32 0 :=
          KernPAlloc.ofNat_ne (a := bq) (b := 0) (by omega) (by decide) (by omega)
        simpa [σc] using h
      have hI2 : ATInv maxpage kl kh db.toPData := by rw [hdb]; exact alloc_at_inv hI hA
      have hu3 : UQ db.AC := by rw [hdb]; exact alloc_usage hu hA
      cases hi1 : ptInsert_spec maxpage num_proc nn vadr bq perm { d with toRData := r1 } with
      | none => rw [hi1] at hs; cases hs
      | some pr2 =>
        obtain ⟨d2, v⟩ := pr2
        rw [hi1] at hs; simp only at hs
        obtain ⟨σd, ld, bd, dd, hrd, hcsd, hMd, hlkd, hfd, r', hsr', hrr'⟩ :=
          ptInsert_triple εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh) nn vadr bq perm σc lb bb db
            hlkc hcsb hMb
            ⟨by simp [σc, Locals.set, frb, hn], by simp [σc, Locals.set, frb, hva], by simp [σc],
              by simp [σc, Locals.set, frb, hpe], hI2, hu3 nn, d2, v, by rw [hdb]; exact hi1⟩
        rw [hdb, hi1] at hsr'
        simp only [Option.some.injEq, Prod.mk.injEq] at hsr'; obtain ⟨hdd, hrr2⟩ := hsr'
        rw [← hdd] at hMd; rw [← hrr2] at hrr'
        obtain ⟨hI4, hu4, hvb⟩ := ptInsert_keeps (by rw [hdb] at hI2; exact hI2) hi1
        have hu5 : UQ d2.AC := hu4 (by rw [hdb] at hu3; exact hu3)
        have hlkd' : (σd "lk").toNat = i0 := by rw [hlkd]; exact hlkc
        have frd : ∀ z : Ident, z = "n2" ∨ z = "vaddr2" ∨ z = "perm2" ∨ z = "padr" → σd z = σc z := by
          intro z hz
          rcases hz with rfl | rfl | rfl | rfl <;> exact hrd.frame rfl
        by_cases hvm : v = maxpage + 1
        · rw [if_pos hvm] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨hdF, hrF⟩ := hs
          rw [hdF] at hMd
          refine ⟨σd, ld, bd, dF, Runs.seq ha0 (Runs.seq hrb (Runs.seq hac (Runs.ite_false (eq_false hne)
            (Runs.seq hrd (Runs.ite_false (ne_false (by rw [hrr', hvm])) Runs.skip))))), hcsd, hMd, ?_,
            fun k hk => by rw [hfd k hk, hfb k (fun h => hk (Or.inl h))], maxpage + 1, by rw [hs0, hrF],
            by rw [hrr', hvm]⟩
          rw [hlkd]; simp [σc, Locals.set, hlkb, σa]
        · rw [if_neg hvm] at hs
          have hner : σd "r" ≠ BitVec.ofNat 32 (maxpage + 1) := by
            rw [hrr']
            exact KernPAlloc.ofNat_ne (a := v) (b := maxpage + 1) (by omega) hmagic hvm
          let σe := ((σd.set "n" (BitVec.ofNat 32 nn')).set "vaddr" (BitVec.ofNat 32 vadr')).set "perm"
            (BitVec.ofNat 32 perm')
          have hae : ∀ {τ : Locals} {lt : RLog}, Runs (rprimsA εR c) (ptInsertS cb maxpage pb fb) σe ld τ lt →
              Runs (rprimsA εR c) (.seq (.assign "n" (.var "n2")) (.seq (.assign "vaddr" (.var "vaddr2"))
                (.seq (.assign "perm" (.var "perm2")) (ptInsertS cb maxpage pb fb)))) σd ld τ lt := by
            intro τ lt hr
            have e1 : (Expr.var "n2").eval σd = BitVec.ofNat 32 nn' := by
              show σd "n2" = _; rw [frd _ (Or.inl rfl)]; simp [σc, Locals.set, frb, hn2]
            have e2 : (Expr.var "vaddr2").eval (σd.set "n" (BitVec.ofNat 32 nn')) = BitVec.ofNat 32 vadr' := by
              show (σd.set "n" (BitVec.ofNat 32 nn')) "vaddr2" = _
              rw [Locals.set_other _ _ (by decide), frd _ (Or.inr (Or.inl rfl))]
              simp [σc, Locals.set, frb, hva2]
            have e3 : (Expr.var "perm2").eval ((σd.set "n" (BitVec.ofNat 32 nn')).set "vaddr"
                (BitVec.ofNat 32 vadr')) = BitVec.ofNat 32 perm' := by
              show ((σd.set "n" (BitVec.ofNat 32 nn')).set "vaddr" (BitVec.ofNat 32 vadr')) "perm2" = _
              rw [Locals.set_other _ _ (by decide), Locals.set_other _ _ (by decide),
                frd _ (Or.inr (Or.inr (Or.inl rfl)))]
              simp [σc, Locals.set, frb, hpe2]
            have h1 := Runs.assign (P := rprimsA εR c) (σ := σd) (l := ld) "n" (.var "n2")
            rw [e1] at h1
            have h2 := Runs.assign (P := rprimsA εR c) (σ := σd.set "n" (BitVec.ofNat 32 nn')) (l := ld)
              "vaddr" (.var "vaddr2")
            rw [e2] at h2
            have h3 := Runs.assign (P := rprimsA εR c)
              (σ := (σd.set "n" (BitVec.ofNat 32 nn')).set "vaddr" (BitVec.ofNat 32 vadr')) (l := ld)
              "perm" (.var "perm2")
            rw [e3] at h3
            exact Runs.seq h1 (Runs.seq h2 (Runs.seq h3 hr))
          have hpadr : σe "padr" = BitVec.ofNat 32 bq := by
            show (((σd.set "n" _).set "vaddr" _).set "perm" _) "padr" = _
            rw [Locals.set_other _ _ (by decide), Locals.set_other _ _ (by decide),
              Locals.set_other _ _ (by decide), frd _ (Or.inr (Or.inr (Or.inr rfl)))]
            simp [σc]
          obtain ⟨σf, lf, bf, df, hrf, hcsf, hMf, hlkf, hff, r'', hsr'', hrr''⟩ :=
            ptInsert_triple εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh) nn' vadr' bq perm' σe ld bd d2
              (by simpa [σe, Locals.set] using hlkd') hcsd hMd
              ⟨by simp [σe, Locals.set], by simp [σe, Locals.set], hpadr, by simp [σe], hI4, hu5 nn',
                dF, rF, hs⟩
          rw [hs] at hsr''
          simp only [Option.some.injEq, Prod.mk.injEq] at hsr''; obtain ⟨hdf, hrf2⟩ := hsr''
          rw [← hdf] at hMf; rw [← hrf2] at hrr''
          refine ⟨σf, lf, bf, dF, Runs.seq ha0 (Runs.seq hrb (Runs.seq hac (Runs.ite_false (eq_false hne)
            (Runs.seq hrd (Runs.ite_true (ne_true hner) (hae hrf)))))), hcsf, hMf, ?_,
            fun k hk => by rw [hff k hk, hfd k hk, hfb k (fun h => hk (Or.inl h))], rF, hs0, hrr''⟩
          rw [hlkf]; simp [σe, Locals.set, hlkd, σc, hlkb, σa]

end Resv2

end MPTNew
