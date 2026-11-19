import CertiKOS.MPTKern

/-!
# mCertiKOS `MPTInit`/`MPTNew`: reserving a page and creating a process's quota, ported

The top of the page-table code (`mcertikos/mm/MPTInitCSource.v`).

Ported from `objects/ObjLMM1.v`: `pt_new_spec`. Ported from
`objects/ObjLMM0.v`: `ptResv_spec`, in the form its C code is verified
against: `container_alloc_spec` followed by `ptInsert_spec`.

Ported from `mm/MPTInitCSource.v`: `pt_new`, `pt_resv`.

Elsewhere: the owner lists that mCertiKOS then puts above the reference
counts are in `PTInitGen.lean`; `pt_resv2` is in `MPTResv2.lean`; `pt_resv`
under the lock, with the invariant carried by the log, is
`MMInv.ptResv_locked_inv`. Not ported: `pmap_init` and `pt_init` (they need
the machine model), and `pt_free`, which the sources leave unused.
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

/-! ## `pt_new` -/

/-- **`pt_new_spec`**: give `q` pages of process `id`'s quota to a new child. -/
def pt_new_spec (num_id mc : Nat) (id q : Nat) (d : PTData) : Option (PTData × Nat) :=
  if d.pg = true ∧ d.ipt = true then
    match container_split_spec num_id mc id q d.toRData with
    | some (r1, i) => some ({ d with toRData := r1 }, i)
    | none => none
  else none

section New
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

theorem split_pperm {mc id q r : Nat} {d d1 : RData} (h : container_split_spec num_id mc id q d = some (d1, r)) :
    d1.pperm = d.pperm := by
  unfold container_split_spec at h
  simp only at h
  by_cases hc : (d.AC id).cused = true ∧ id * mc + 1 + (d.AC id).cchildren.length < num_id ∧
      (d.AC id).cchildren.length < mc ∧ q + (d.AC id).cusage ≤ (d.AC id).cquota
  · rw [if_pos hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
  · rw [if_neg hc] at h; cases h

/-- **`container_split` in the state with page tables.** -/
theorem container_split_lift (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : Layout maxpage num_id cb num_proc pb ib fb) (hnum : cb + 5 * num_id < 2 ^ 32)
    (mc id q : Nat) (hid : id < num_id) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => cb ≤ k ∧ k < cb + 5 * num_id)
      (fun σ d => σ "id" = BitVec.ofNat 32 id ∧ σ "amt" = BitVec.ofNat 32 q ∧
        ∃ d1 r, container_split_spec num_id mc id q d.toRData = some (d1, r))
      (ctSplitCS cb (BitVec.ofNat 32 mc))
      (fun _ d σ' d' => ∃ r1 : RData, d' = { d with toRData := r1 } ∧
        ∃ r, container_split_spec num_id mc id q d.toRData = some (r1, r) ∧ σ' "r" = BitVec.ofNat 32 r) := by
  have := hL.hcb; have := hL.hpb
  refine ((container_split_triple εR c i0 (maxpage := maxpage) hL.hcb hnum mc id q hid).lift
    (π := PTData.toRData)
    (put := fun (d' : PTData) (r1 : RData) => ({ d' with toRData := r1 } : PTData))
    (M2 := MatchPT num_proc pb ib fb ida) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.mm, h.pt⟩, fun h => ⟨h.1, h.2⟩⟩)
  intro d' b σ σ' d1 b' h2 hM hP hQ hf
  obtain ⟨r, hs, -⟩ := hQ
  refine matchpt_transfer hL h2 (fun k hk => hf k (by omega)) rfl rfl rfl (fun pi n i hh => ?_)
  show d1.pperm pi = d'.pperm pi
  rw [split_pperm hs]

/-- `pt_new(id, quota)`: `return container_split(id, quota);` -/
def ptNewS (cb mc : Nat) : Stmt APrim := ctSplitCS cb (BitVec.ofNat 32 mc)

/-- **`pt_new` refines `pt_new_spec`.** -/
theorem ptNew_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hnum : cb + 5 * num_id < 2 ^ 32) (mc id q : Nat) (hid : id < num_id) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => cb ≤ k ∧ k < cb + 5 * num_id)
      (fun σ d => σ "id" = BitVec.ofNat 32 id ∧ σ "amt" = BitVec.ofNat 32 q ∧
        ∃ d1 r, pt_new_spec num_id mc id q d = some (d1, r))
      (ptNewS cb mc)
      (fun _ d σ' d' => ∃ r, pt_new_spec num_id mc id q d = some (d', r) ∧ σ' "r" = BitVec.ofNat 32 r) := by
  refine (container_split_lift εR c i0 hL hnum mc id q hid).conseq ?_ ?_
  · intro σ d ⟨h1, h2, d1, r, hs⟩
    refine ⟨h1, h2, ?_⟩
    unfold pt_new_spec at hs
    by_cases hc : d.pg = true ∧ d.ipt = true
    · rw [if_pos hc] at hs
      cases hsp : container_split_spec num_id mc id q d.toRData with
      | none => rw [hsp] at hs; cases hs
      | some pr => exact ⟨pr.1, pr.2, rfl⟩
    · rw [if_neg hc] at hs; cases hs
  · intro σ d σ' d' ⟨_, _, d1, r, hs⟩ ⟨r1, hd', r', hsp, hr⟩
    refine ⟨r', ?_, hr⟩
    unfold pt_new_spec at hs ⊢
    by_cases hc : d.pg = true ∧ d.ipt = true
    · rw [if_pos hc, hsp, hd']
    · rw [if_neg hc] at hs; cases hs

end New

/-! ## `pt_resv` -/

/-- **`ptResv_spec`**: allocate a page from process `n`'s quota and map it at
`vadr`. Returns `MagicNumber` if no page could be allocated. -/
def ptResv_spec (maxpage num_proc : Nat) (n vadr perm : Nat) (d : PTData) : Option (PTData × Nat) :=
  match container_alloc_spec n d.toRData with
  | some (r1, b) =>
    if b = 0 then some (d, maxpage + 1)
    else ptInsert_spec maxpage num_proc n vadr b perm { d with toRData := r1 }
  | none => none

/-- What `container_alloc_spec` returns: 0 and no change, or a page below `nps`
with the container still within its quota. -/
theorem alloc_facts {d r1 : RData} {id b : Nat} (hu : (d.AC id).cusage ≤ (d.AC id).cquota)
    (h : container_alloc_spec id d = some (r1, b)) :
    (b = 0 ∧ r1 = d) ∨ (0 < b ∧ b < d.nps ∧ (r1.AC id).cusage ≤ (r1.AC id).cquota) := by
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
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h0, hn, -, -⟩ := first_free_some hff
        refine Or.inr ⟨h0, hn, ?_⟩
        simp only [setAt_eq]; omega
    · rw [if_neg hlt] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
  · rw [if_neg hiu] at h; cases h

/-- ```
pi = container_alloc(n);
if (pi == 0) result = MagicNumber;
else result = pt_insert(n, vaddr, pi, perm);
return result;
``` -/
def ptResvS (cb maxpage pb fb : Nat) : Stmt APrim :=
  .seq (.assign "id" (.var "n")) (.seq (ctAllocCS cb maxpage) (.seq (.assign "padr" (.var "r"))
    (.ite (.bin .eq (.var "padr") (.const 0)) (.assign "r" (.const (BitVec.ofNat 32 (maxpage + 1))))
      (ptInsertS cb maxpage pb fb))))

section Resv
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **`pt_resv` refines `ptResv_spec`.** -/
theorem ptResv_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (nn vadr perm : Nat) (hnid : nn < num_id) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => k < cb + 5 * num_id ∨ pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        σ "perm" = BitVec.ofNat 32 perm ∧ ATInv maxpage kl kh d.toPData ∧
        (d.AC nn).cusage ≤ (d.AC nn).cquota ∧
        ∃ d1 r, ptResv_spec maxpage num_proc nn vadr perm d = some (d1, r))
      (ptResvS cb maxpage pb fb)
      (fun _ d σ' d' => ∃ r, ptResv_spec maxpage num_proc nn vadr perm d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hn, hva, hpe, hI, hu, dF, rF, hs⟩
  have hs0 := hs
  unfold ptResv_spec at hs
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
        (by simpa [σa, Locals.set] using hlk) hcs hM ⟨by simp [σa], hI, hu, _, _, hA⟩
    rw [hA] at hsr
    simp only [Option.some.injEq, Prod.mk.injEq] at hsr; obtain ⟨hr1, hrb'⟩ := hsr
    rw [← hr1] at hdb; rw [← hrb'] at hrr
    have frb : ∀ z : Ident, z = "n" ∨ z = "vaddr" ∨ z = "perm" → σb z = σ z := by
      intro z hz
      have h1 : σb z = σa z := by
        rcases hz with rfl | rfl | rfl <;>
          exact hrb.frame (by simp [frS, ctAllocCS, pallocCS, getNpsS, pallocLoop, loopBody, isNormS, atGetS,
            atSetS, atSetCS])
      rw [h1]
      rcases hz with rfl | rfl | rfl <;> simp [σa, Locals.set]
    let σc := σb.set "padr" (BitVec.ofNat 32 bq)
    have hac : Runs (rprimsA εR c) (.assign "padr" (.var "r")) σb lb σc lb := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σb) (l := lb) "padr" (.var "r")
      have e : (Expr.var "r").eval σb = BitVec.ofNat 32 bq := hrr
      rw [e] at h; exact h
    have hlkc : (σc "lk").toNat = i0 := by simp [σc, Locals.set, hlkb, σa, hlk]
    rcases alloc_facts hu hA with ⟨hb0, hr1d⟩ | ⟨hbpos, hblt, hu2⟩
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
      obtain ⟨σd, ld, bd, dd, hrd, hcsd, hMd, hlkd, hfd, r', hsr', hrr'⟩ :=
        ptInsert_triple εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh) nn vadr bq perm σc lb bb db
          hlkc hcsb hMb
          ⟨by simp [σc, Locals.set, frb, hn], by simp [σc, Locals.set, frb, hva], by simp [σc],
            by simp [σc, Locals.set, frb, hpe], hI2, by rw [hdb]; exact hu2, dF, rF, by rw [hdb]; exact hs⟩
      rw [hdb, hs] at hsr'
      simp only [Option.some.injEq, Prod.mk.injEq] at hsr'; obtain ⟨hdd, hrr2⟩ := hsr'
      rw [← hdd] at hMd; rw [← hrr2] at hrr'
      refine ⟨σd, ld, bd, dF, Runs.seq ha0 (Runs.seq hrb (Runs.seq hac (Runs.ite_false (eq_false hne) hrd))),
        hcsd, hMd, ?_, fun k hk => by rw [hfd k hk, hfb k (fun h => hk (Or.inl h))], rF, hs0, hrr'⟩
      rw [hlkd]; simp [σc, Locals.set, hlkb, σa]

end Resv

end MPTNew
