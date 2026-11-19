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

/-! ## `quota_bounded_AT` -/

/-- What container `c` may still allocate. -/
def qterm (c : Container) : Nat := if c.cused = true then c.cquota - c.cusage else 0

/-- `sum_quotas ac i`: the unused quota of containers `0..i`. -/
def sum_quotas (ac : ContainerPool) : Nat → Nat
  | 0 => qterm (ac 0)
  | i + 1 => qterm (ac (i + 1)) + sum_quotas ac i

def pterm (x : ATInfo) : Nat := if isFree x = true then 1 else 0

/-- `unused_pages_AT AT p`: the free normal pages among `1..p`. -/
def unused_pages_AT (AT : ATable) : Nat → Nat
  | 0 => 0
  | p + 1 => pterm (AT (p + 1)) + unused_pages_AT AT p

/-- **`quota_bounded_AT`**: the quota still promised to containers is covered
by free pages. -/
def quota_bounded_AT (num_id : Nat) (ac : ContainerPool) (AT : ATable) (nps : Nat) : Prop :=
  sum_quotas ac (num_id - 1) ≤ unused_pages_AT AT (nps - 1)

theorem sum_outside (ac : ContainerPool) (i : Nat) (c : Container) :
    ∀ n, n < i → sum_quotas (setAt ac i c) n = sum_quotas ac n
  | 0, h => by simp only [sum_quotas, setAt_ne _ _ (show (0 : Nat) ≠ i by omega)]
  | n + 1, h => by
    simp only [sum_quotas, setAt_ne _ _ (show n + 1 ≠ i by omega)]
    rw [sum_outside ac i c n (by omega)]

/-- Changing one container changes the sum by the difference of its terms. -/
theorem sum_set (ac : ContainerPool) (i : Nat) (c : Container) :
    ∀ n, i ≤ n → sum_quotas (setAt ac i c) n + qterm (ac i) = sum_quotas ac n + qterm c
  | 0, h => by
    have e : i = 0 := by omega
    subst e; simp only [sum_quotas, setAt_eq]; omega
  | n + 1, h => by
    by_cases e : i = n + 1
    · subst e; simp only [sum_quotas, setAt_eq]
      rw [sum_outside ac (n + 1) c n (by omega)]; omega
    · simp only [sum_quotas, setAt_ne _ _ (show n + 1 ≠ i from fun x => e x.symm)]
      have := sum_set ac i c n (by omega); omega

theorem sum_ge (ac : ContainerPool) (i : Nat) : ∀ n, i ≤ n → qterm (ac i) ≤ sum_quotas ac n
  | 0, h => by have e : i = 0 := by omega
               subst e; exact Nat.le_refl _
  | n + 1, h => by
    simp only [sum_quotas]
    by_cases e : i = n + 1
    · subst e; omega
    · have := sum_ge ac i n (by omega); omega

theorem unused_outside (AT : ATable) (i : Nat) (x : ATInfo) :
    ∀ p, p < i → unused_pages_AT (setAt AT i x) p = unused_pages_AT AT p
  | 0, _ => rfl
  | p + 1, h => by
    simp only [unused_pages_AT, setAt_ne _ _ (show p + 1 ≠ i by omega)]
    rw [unused_outside AT i x p (by omega)]

theorem unused_set (AT : ATable) (i : Nat) (x : ATInfo) (hi : 0 < i) :
    ∀ p, i ≤ p → unused_pages_AT (setAt AT i x) p + pterm (AT i) = unused_pages_AT AT p + pterm x
  | 0, h => by omega
  | p + 1, h => by
    by_cases e : i = p + 1
    · subst e; simp only [unused_pages_AT, setAt_eq]
      rw [unused_outside AT (p + 1) x p (by omega)]; omega
    · simp only [unused_pages_AT, setAt_ne _ _ (show p + 1 ≠ i from fun y => e y.symm)]
      have := unused_set AT i x hi p (by omega); omega

theorem unused_zero (AT : ATable) : ∀ p, (∀ x, 0 < x → x ≤ p → isFree (AT x) = false) →
    unused_pages_AT AT p = 0
  | 0, _ => rfl
  | p + 1, h => by
    simp only [unused_pages_AT, pterm, h (p + 1) (by omega) (Nat.le_refl _)]
    rw [unused_zero AT p (fun x h1 h2 => h x h1 (by omega))]; simp

section Quota
variable {num_id mc : Nat}

/-- **A container below its quota finds a free page**
(`quota_bounded_AT_first_free`). -/
theorem quota_first_free {ac : ContainerPool} {AT : ATable} {nps id : Nat}
    (hv : Container_valid num_id mc ac) (hb : quota_bounded_AT num_id ac AT nps)
    (hu : (ac id).cused = true) (hlt : (ac id).cusage < (ac id).cquota) :
    ∃ i, first_free AT nps = some i := by
  cases hff : first_free AT nps with
  | some i => exact ⟨i, rfl⟩
  | none =>
    exfalso
    have h0 : unused_pages_AT AT (nps - 1) = 0 := unused_zero AT _ (fun x h1 h2 => by
      have := ffFrom_none hff x (by omega) (by omega); exact this)
    have h1 := sum_ge ac id (num_id - 1) (by have := hv.cvalid_id id hu; omega)
    have h2 : 1 ≤ qterm (ac id) := by simp only [qterm, if_pos hu]; omega
    unfold quota_bounded_AT at hb; omega

/-- **Under the invariants `container_alloc_spec` is defined.** -/
theorem alloc_defined {d : RData} {id : Nat} (hv : Container_valid num_id mc d.AC)
    (hb : quota_bounded_AT num_id d.AC d.AT d.nps) (hin : d.init = true) (hu : (d.AC id).cused = true) :
    ∃ d' r, container_alloc_spec id d = some (d', r) := by
  unfold container_alloc_spec
  simp only
  rw [if_pos ⟨hin, hu⟩]
  by_cases hlt : (d.AC id).cusage < (d.AC id).cquota
  · rw [if_pos hlt]
    obtain ⟨i, hi⟩ := quota_first_free hv hb hu hlt
    rw [hi]; exact ⟨_, _, rfl⟩
  · rw [if_neg hlt]; exact ⟨_, _, rfl⟩

/-- **`container_alloc_spec` preserves `quota_bounded_AT`.** -/
theorem alloc_quota_bounded {d d' : RData} {id r : Nat} (hv : Container_valid num_id mc d.AC)
    (hb : quota_bounded_AT num_id d.AC d.AT d.nps) (hs : container_alloc_spec id d = some (d', r)) :
    quota_bounded_AT num_id d'.AC d'.AT d'.nps := by
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
        obtain ⟨hi0, hin', hfree, -⟩ := first_free_some hff
        have h1 := sum_set d.AC id ⟨(d.AC id).cquota, (d.AC id).cusage + 1, (d.AC id).cparent,
          (d.AC id).cchildren, (d.AC id).cused⟩ (num_id - 1) (by have := hv.cvalid_id id hiu.2; omega)
        have h2 := unused_set d.AT i (.ATValid true .ATNorm 0) hi0 (d.nps - 1) (by omega)
        have e1 : qterm (d.AC id) = (d.AC id).cquota - (d.AC id).cusage := by simp only [qterm, if_pos hiu.2]
        have e2 : qterm ⟨(d.AC id).cquota, (d.AC id).cusage + 1, (d.AC id).cparent, (d.AC id).cchildren,
            (d.AC id).cused⟩ = (d.AC id).cquota - ((d.AC id).cusage + 1) := by simp only [qterm, if_pos hiu.2]
        have e3 : pterm (d.AT i) = 1 := by simp only [pterm, (isFree_iff _).2 hfree, if_true]
        have e4 : pterm (.ATValid true .ATNorm 0) = 0 := rfl
        unfold quota_bounded_AT at hb ⊢
        show sum_quotas (setAt d.AC id _) (num_id - 1) ≤ unused_pages_AT (setAt d.AT i _) (d.nps - 1)
        omega
    · rw [if_neg hlt] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs; exact hb
  · rw [if_neg hiu] at hs; cases hs

/-- **`container_split_spec` preserves `quota_bounded_AT`.** The quota moves
from the parent to the child. -/
theorem split_quota_bounded {d d' : RData} {id q r : Nat} (hv : Container_valid num_id mc d.AC)
    (hb : quota_bounded_AT num_id d.AC d.AT d.nps)
    (hs : container_split_spec num_id mc id q d = some (d', r)) :
    quota_bounded_AT num_id d'.AC d'.AT d'.nps := by
  unfold container_split_spec at hs
  simp only at hs
  by_cases hc : (d.AC id).cused = true ∧ id * mc + 1 + (d.AC id).cchildren.length < num_id ∧
      (d.AC id).cchildren.length < mc ∧ q + (d.AC id).cusage ≤ (d.AC id).cquota
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
    obtain ⟨hused, hilt, hLmc, hqu⟩ := hc
    have hmul : id ≤ id * mc := Nat.le_mul_of_pos_right _ (by omega)
    -- the child slot was free
    have hIun : ¬ (d.AC (id * mc + 1 + (d.AC id).cchildren.length)).cused = true := by
      intro hcu
      have hp := hv.cvalid_parent_id _ hcu
      have hdiv : (id * mc + 1 + (d.AC id).cchildren.length - 1) / mc = id := by
        have e : id * mc + 1 + (d.AC id).cchildren.length - 1 = (d.AC id).cchildren.length + mc * id := by
          rw [Nat.mul_comm]; omega
        rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < mc), Nat.div_eq_of_lt hLmc]; omega
      rw [if_neg (by omega), hdiv] at hp
      have hm := hv.cvalid_parents_child _ hcu (by omega)
      rw [hp] at hm
      have := (hv.cvalid_child_id_range id hused _ hm).2
      omega
    have h1 := sum_set d.AC id ⟨(d.AC id).cquota, (d.AC id).cusage + q, (d.AC id).cparent,
      (id * mc + 1 + (d.AC id).cchildren.length) :: (d.AC id).cchildren, (d.AC id).cused⟩ (num_id - 1)
      (by have := hv.cvalid_id id hused; omega)
    have h2 := sum_set (setAt d.AC id ⟨(d.AC id).cquota, (d.AC id).cusage + q, (d.AC id).cparent,
      (id * mc + 1 + (d.AC id).cchildren.length) :: (d.AC id).cchildren, (d.AC id).cused⟩)
      (id * mc + 1 + (d.AC id).cchildren.length) ⟨q, 0, id, [], true⟩ (num_id - 1) (by omega)
    rw [setAt_ne _ _ (show id * mc + 1 + (d.AC id).cchildren.length ≠ id by omega)] at h2
    have e1 : qterm (d.AC id) = (d.AC id).cquota - (d.AC id).cusage := by simp only [qterm, if_pos hused]
    have e2 : qterm ⟨(d.AC id).cquota, (d.AC id).cusage + q, (d.AC id).cparent,
        (id * mc + 1 + (d.AC id).cchildren.length) :: (d.AC id).cchildren, (d.AC id).cused⟩ =
        (d.AC id).cquota - ((d.AC id).cusage + q) := by simp only [qterm, if_pos hused]
    have e3 : qterm (d.AC (id * mc + 1 + (d.AC id).cchildren.length)) = 0 := by
      simp only [qterm, if_neg hIun]
    have e4 : qterm ⟨q, 0, id, [], true⟩ = q := by simp [qterm]
    unfold quota_bounded_AT at hb ⊢
    show sum_quotas (setAt (setAt d.AC id _) _ _) (num_id - 1) ≤ unused_pages_AT d.AT (d.nps - 1)
    omega
  · rw [if_neg hc] at hs; cases hs

/-- **`container_alloc_spec` preserves the allocation-table invariant.** -/
theorem alloc_at_inv {maxpage kl kh : Nat} {d d' : RData} {id r : Nat}
    (hI : ATInv maxpage kl kh d.toPData) (hs : container_alloc_spec id d = some (d', r)) :
    ATInv maxpage kl kh d'.toPData := by
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
        have hp : palloc'_spec d.toPData = some ({ d.toPData with
            AT := setAt d.AT i (.ATValid true .ATNorm 0), pperm := setAt d.pperm i .PGAlloc }, i) := by
          simp [palloc'_spec, hiu.1, hff]
        exact palloc_inv hI hp
    · rw [if_neg hlt] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs; exact hI
  · rw [if_neg hiu] at hs; cases hs

end Quota

end MContainer
