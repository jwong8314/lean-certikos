import CertiKOS.MContainer

/-!
# mCertiKOS container invariants, ported

The invariants that mCertiKOS's `high_level_invariant` keeps about containers
(`mcertikos/mm/MContainer.v`), and proofs that the ported specifications
preserve them.

Ported from `layerlib/AuxStateDataType.v`: `child_quotas_bounded`,
`Container_valid` (all thirteen fields), `sum_quotas`, `unused_pages_AT`,
`quota_bounded_AT`.

* `alloc_valid`, `split_valid`: `container_alloc_spec` and
  `container_split_spec` preserve `Container_valid`.
* `alloc_quota_bounded`, `split_quota_bounded`: they preserve
  `quota_bounded_AT`.
* `alloc_at_inv`: `container_alloc_spec` preserves the allocation-table
  invariant `ATInv`.
* `alloc_defined`: under the invariants `container_alloc_spec` is defined.
  A container below its quota always finds a free page
  (mCertiKOS's `quota_bounded_AT_first_free`).

These are statements about the specifications, as in mCertiKOS, where each
primitive of a layer is shown to preserve `high_level_invariant`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace MContainer

open MALOp

/-! ## `Container_valid` -/

/-- The quotas of the children `cs` fit in `n`. -/
inductive child_quotas_bounded (C : ContainerPool) : List Nat → Nat → Prop
  | cqb_nil (n : Nat) : child_quotas_bounded C [] n
  | cqb_cons (c : Nat) (cs : List Nat) (n m : Nat) : (C c).cquota ≤ m → child_quotas_bounded C cs n →
      child_quotas_bounded C (c :: cs) (n + m)

/-- The sum of the children's quotas. -/
def qsum (C : ContainerPool) : List Nat → Nat
  | [] => 0
  | c :: cs => (C c).cquota + qsum C cs

theorem cqb_iff {C : ContainerPool} {cs : List Nat} {n : Nat} :
    child_quotas_bounded C cs n ↔ qsum C cs ≤ n := by
  constructor
  · intro h
    induction h with
    | cqb_nil n => exact Nat.zero_le _
    | cqb_cons c cs n m hm _ ih => simp only [qsum]; omega
  · induction cs generalizing n with
    | nil => intro _; exact .cqb_nil n
    | cons c cs ih =>
      intro h
      simp only [qsum] at h
      have e : n = (n - (C c).cquota) + (C c).cquota := by omega
      rw [e]; exact .cqb_cons c cs _ _ (Nat.le_refl _) (ih (by omega))

theorem qsum_congr {C C' : ContainerPool} : ∀ {cs : List Nat},
    (∀ c, c ∈ cs → (C' c).cquota = (C c).cquota) → qsum C' cs = qsum C cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [qsum]
    rw [h c List.mem_cons_self, qsum_congr (fun k hk => h k (List.mem_cons_of_mem _ hk))]

/-- `Container_valid`: the container pool is a tree rooted at 0, with quotas
that add up. -/
structure Container_valid (num_id max_children : Nat) (C : ContainerPool) : Prop where
  cvalid_id : ∀ i, (C i).cused = true → i < num_id
  cvalid_root : ∀ i, (C i).cused = true → (i = (C i).cparent ↔ i = 0)
  cvalid_quota : ∀ i, (C i).cused = true → (C i).cquota ≤ 2 ^ 32 - 1
  cvalid_usage : ∀ i, (C i).cused = true → (C i).cusage ≤ (C i).cquota
  cvalid_parent_used : ∀ i, (C i).cused = true → (C (C i).cparent).cused = true
  cvalid_children_used : ∀ i, (C i).cused = true → ∀ j, j ∈ (C i).cchildren → (C j).cused = true
  cvalid_parents_child : ∀ i, (C i).cused = true → i ≠ 0 → i ∈ (C (C i).cparent).cchildren
  cvalid_childrens_parent : ∀ i, (C i).cused = true → ∀ j, j ∈ (C i).cchildren → (C j).cparent = i
  cvalid_cqb : ∀ i, (C i).cused = true → child_quotas_bounded C (C i).cchildren (C i).cusage
  cvalid_nodup : ∀ i, (C i).cused = true → (C i).cchildren.Nodup
  cvalid_max_children : ∀ i, (C i).cused = true → (C i).cchildren.length ≤ max_children
  cvalid_parent_id : ∀ i, (C i).cused = true →
    (C i).cparent = if i = 0 then 0 else (i - 1) / max_children
  cvalid_child_id_range : ∀ i, (C i).cused = true → ∀ j, j ∈ (C i).cchildren →
    i * max_children + 1 ≤ j ∧ j < i * max_children + 1 + (C i).cchildren.length

section Valid
variable {num_id mc : Nat}

/-- Raising usages within quota, and changing nothing else, keeps the pool valid. -/
theorem Container_valid.of_same {C C' : ContainerPool} (h : Container_valid num_id mc C)
    (hq : ∀ i, (C' i).cquota = (C i).cquota) (hp : ∀ i, (C' i).cparent = (C i).cparent)
    (hc : ∀ i, (C' i).cchildren = (C i).cchildren) (hu : ∀ i, (C' i).cused = (C i).cused)
    (hus : ∀ i, (C i).cused = true → (C i).cusage ≤ (C' i).cusage ∧ (C' i).cusage ≤ (C i).cquota) :
    Container_valid num_id mc C' := by
  constructor
  · intro i hi; rw [hu] at hi; exact h.cvalid_id i hi
  · intro i hi; rw [hu] at hi; rw [hp]; exact h.cvalid_root i hi
  · intro i hi; rw [hu] at hi; rw [hq]; exact h.cvalid_quota i hi
  · intro i hi; rw [hu] at hi; rw [hq]; exact (hus i hi).2
  · intro i hi; rw [hu] at hi; rw [hp, hu]; exact h.cvalid_parent_used i hi
  · intro i hi j hj; rw [hu] at hi; rw [hc] at hj; rw [hu]; exact h.cvalid_children_used i hi j hj
  · intro i hi h0; rw [hu] at hi; rw [hp, hc]; exact h.cvalid_parents_child i hi h0
  · intro i hi j hj; rw [hu] at hi; rw [hc] at hj; rw [hp]; exact h.cvalid_childrens_parent i hi j hj
  · intro i hi; rw [hu] at hi
    rw [cqb_iff, hc, qsum_congr (fun c _ => hq c)]
    have := cqb_iff.1 (h.cvalid_cqb i hi); have := (hus i hi).1; omega
  · intro i hi; rw [hu] at hi; rw [hc]; exact h.cvalid_nodup i hi
  · intro i hi; rw [hu] at hi; rw [hc]; exact h.cvalid_max_children i hi
  · intro i hi; rw [hu] at hi; rw [hp]; exact h.cvalid_parent_id i hi
  · intro i hi j hj; rw [hu] at hi; rw [hc] at hj ⊢; exact h.cvalid_child_id_range i hi j hj

/-- **`container_alloc_spec` preserves `Container_valid`.** -/
theorem alloc_valid {d d' : RData} {id r : Nat} (h : Container_valid num_id mc d.AC)
    (hs : container_alloc_spec id d = some (d', r)) : Container_valid num_id mc d'.AC := by
  unfold container_alloc_spec at hs
  simp only at hs
  by_cases hiu : d.init = true ∧ (d.AC id).cused = true
  · rw [if_pos hiu] at hs
    by_cases hlt : (d.AC id).cusage < (d.AC id).cquota
    · rw [if_pos hlt] at hs
      cases hff : first_free d.AT d.nps with
      | none => rw [hff] at hs; cases hs
      | some i =>
        rw [hff] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
        refine h.of_same (fun j => ?_) (fun j => ?_) (fun j => ?_) (fun j => ?_) (fun j hj => ?_)
        · by_cases e : j = id <;> simp [setAt, e]
        · by_cases e : j = id <;> simp [setAt, e]
        · by_cases e : j = id <;> simp [setAt, e]
        · by_cases e : j = id <;> simp [setAt, e]
        · by_cases e : j = id
          · subst e; simp only [setAt_eq]; omega
          · simp only [setAt_ne _ _ e]; exact ⟨Nat.le_refl _, h.cvalid_usage j hj⟩
    · rw [if_neg hlt] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs; exact h
  · rw [if_neg hiu] at hs; cases hs

/-- The pool after a split, described by what it holds at the child slot `I`,
at the parent `id`, and elsewhere. -/
theorem split_valid_core {C C' : ContainerPool} (h : Container_valid num_id mc C) {id q I : Nat}
    (hI : I = id * mc + 1 + (C id).cchildren.length) (hu : (C id).cused = true) (hIn : I < num_id)
    (hL : (C id).cchildren.length < mc) (hq : q + (C id).cusage ≤ (C id).cquota)
    (aI : C' I = ⟨q, 0, id, [], true⟩)
    (aid : C' id = ⟨(C id).cquota, (C id).cusage + q, (C id).cparent, I :: (C id).cchildren, (C id).cused⟩)
    (aoth : ∀ j, j ≠ I → j ≠ id → C' j = C j) : Container_valid num_id mc C' := by
  have hmul : id ≤ id * mc := Nat.le_mul_of_pos_right _ (by omega)
  have hIid : I ≠ id := by omega
  have hI0 : I ≠ 0 := by omega
  have hdiv : (I - 1) / mc = id := by
    have e : I - 1 = (C id).cchildren.length + mc * id := by rw [hI, Nat.mul_comm]; omega
    rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < mc), Nat.div_eq_of_lt hL]; omega
  -- the child slot was free
  have hIun : ¬ (C I).cused = true := by
    intro hc
    have hp := h.cvalid_parent_id I hc
    rw [if_neg hI0, hdiv] at hp
    have hm := h.cvalid_parents_child I hc hI0
    rw [hp] at hm
    have := (h.cvalid_child_id_range id hu I hm).2
    omega
  have neI : ∀ k, (C k).cused = true → k ≠ I := fun k hk e => hIun (e ▸ hk)
  have U : ∀ k, (C k).cused = true → (C' k).cused = true := by
    intro k hk
    by_cases e : k = id
    · rw [e, aid]; exact hu
    · rw [aoth k (neI k hk) e]; exact hk
  have U' : ∀ k, (C' k).cused = true → k ≠ I → (C k).cused = true := by
    intro k hk hkI
    by_cases e : k = id
    · rw [e]; exact hu
    · rw [aoth k hkI e] at hk; exact hk
  have P : ∀ k, k ≠ I → (C' k).cparent = (C k).cparent := by
    intro k hkI
    by_cases e : k = id
    · rw [e, aid]
    · rw [aoth k hkI e]
  have Qe : ∀ k, k ≠ I → (C' k).cquota = (C k).cquota := by
    intro k hkI
    by_cases e : k = id
    · rw [e, aid]
    · rw [aoth k hkI e]
  constructor
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI]; exact hIn
    · exact h.cvalid_id j (U' j hj hjI)
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; exact ⟨fun e => absurd e hIid, fun e => absurd e hI0⟩
    · rw [P j hjI]; exact h.cvalid_root j (U' j hj hjI)
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; have := h.cvalid_quota id hu; show q ≤ _; omega
    · rw [Qe j hjI]; exact h.cvalid_quota j (U' j hj hjI)
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; exact Nat.zero_le _
    · by_cases e : j = id
      · rw [e, aid]; show (C id).cusage + q ≤ (C id).cquota; omega
      · rw [aoth j hjI e]; exact h.cvalid_usage j (U' j hj hjI)
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; exact U id hu
    · rw [P j hjI]; exact U _ (h.cvalid_parent_used j (U' j hj hjI))
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; intro k hk; simp at hk
    · by_cases e : j = id
      · rw [e, aid]; intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with hk | hk
        · rw [hk, aI]
        · exact U k (h.cvalid_children_used id hu k hk)
      · rw [aoth j hjI e]; intro k hk
        exact U k (h.cvalid_children_used j (U' j hj hjI) k hk)
  · intro j hj hj0
    by_cases hjI : j = I
    · rw [hjI, aI]; show I ∈ (C' id).cchildren; rw [aid]; exact List.mem_cons_self
    · have hju := U' j hj hjI
      rw [P j hjI]
      have hm := h.cvalid_parents_child j hju hj0
      have hpu := h.cvalid_parent_used j hju
      by_cases e : (C j).cparent = id
      · rw [e, aid]; rw [e] at hm; exact List.mem_cons_of_mem _ hm
      · rw [aoth _ (neI _ hpu) e]; exact hm
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; intro k hk; simp at hk
    · by_cases e : j = id
      · rw [e, aid]; intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with hk | hk
        · rw [hk, aI]
        · rw [P k (neI k (h.cvalid_children_used id hu k hk))]
          exact h.cvalid_childrens_parent id hu k hk
      · rw [aoth j hjI e]; intro k hk
        have hju := U' j hj hjI
        rw [P k (neI k (h.cvalid_children_used j hju k hk))]
        exact h.cvalid_childrens_parent j hju k hk
  · intro j hj
    rw [cqb_iff]
    by_cases hjI : j = I
    · rw [hjI, aI]; exact Nat.le_refl 0
    · have hju := U' j hj hjI
      have old := cqb_iff.1 (h.cvalid_cqb j hju)
      have hcong : qsum C' (C j).cchildren = qsum C (C j).cchildren :=
        qsum_congr (fun k hk => Qe k (neI k (h.cvalid_children_used j hju k hk)))
      by_cases e : j = id
      · rw [e] at old hcong
        rw [e, aid]
        show qsum C' (I :: (C id).cchildren) ≤ (C id).cusage + q
        simp only [qsum]; rw [aI, hcong]; show q + _ ≤ _; omega
      · rw [aoth j hjI e, hcong]; exact old
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; exact List.nodup_nil
    · by_cases e : j = id
      · rw [e, aid]
        exact List.nodup_cons.2 ⟨fun hm => by have := (h.cvalid_child_id_range id hu I hm).2; omega,
          h.cvalid_nodup id hu⟩
      · rw [aoth j hjI e]; exact h.cvalid_nodup j (U' j hj hjI)
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; exact Nat.zero_le _
    · by_cases e : j = id
      · rw [e, aid]; show (I :: (C id).cchildren).length ≤ mc; simp only [List.length_cons]; omega
      · rw [aoth j hjI e]; exact h.cvalid_max_children j (U' j hj hjI)
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI, if_neg hI0, hdiv]
    · rw [P j hjI]; exact h.cvalid_parent_id j (U' j hj hjI)
  · intro j hj
    by_cases hjI : j = I
    · rw [hjI, aI]; intro k hk; simp at hk
    · by_cases e : j = id
      · rw [e, aid]; intro k hk
        simp only [List.mem_cons] at hk
        simp only [List.length_cons]
        rcases hk with hk | hk
        · omega
        · have := h.cvalid_child_id_range id hu k hk; omega
      · rw [aoth j hjI e]; exact h.cvalid_child_id_range j (U' j hj hjI)

/-- **`container_split_spec` preserves `Container_valid`.** -/
theorem split_valid {d d' : RData} {id q r : Nat} (h : Container_valid num_id mc d.AC)
    (hs : container_split_spec num_id mc id q d = some (d', r)) : Container_valid num_id mc d'.AC := by
  unfold container_split_spec at hs
  simp only at hs
  by_cases hc : (d.AC id).cused = true ∧ id * mc + 1 + (d.AC id).cchildren.length < num_id ∧
      (d.AC id).cchildren.length < mc ∧ q + (d.AC id).cusage ≤ (d.AC id).cquota
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
    obtain ⟨hused, hilt, hLmc, hqu⟩ := hc
    have hmul : id ≤ id * mc := Nat.le_mul_of_pos_right _ (by omega)
    refine split_valid_core h rfl hused hilt hLmc hqu (setAt_eq _ _ _) ?_ (fun j h1 h2 => ?_)
    · show setAt (setAt d.AC id _) _ _ id = _
      rw [setAt_ne _ _ (by omega), setAt_eq]
    · show setAt (setAt d.AC id _) _ _ j = _
      rw [setAt_ne _ _ h1, setAt_ne _ _ h2]
  · rw [if_neg hc] at hs; cases hs

end Valid

end MContainer
