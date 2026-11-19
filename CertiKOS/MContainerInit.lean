import CertiKOS.MALInit
import CertiKOS.MContainerInv

/-!
# mCertiKOS `container_init`: the initial container, ported

`container_init` runs `mem_init` and then creates the root container, whose
quota is the number of free pages.

Ported from `clib/RealParams.v`: `real_quota` (as `real_quota_AT`),
`real_AC`, and `real_quota_unused_pages_AT`.

Ported from `objects/ObjContainer.v`: `container_init_spec`.

* `container_init_inv`: **`container_init_spec` establishes all three
  invariants** of the memory-management layers ported so far: the
  allocation-table invariant, `Container_valid`, and `quota_bounded_AT`.
  With the preservation theorems of `MContainerInv.lean` and `MALOp.lean`,
  the invariants now hold from boot onwards, at the level of the
  specifications.

Not here yet: the C code of `container_init` (a loop counting the free
pages).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MContainer

open MALOp MALInit

/-- `Container_unused`. -/
def Container_unused : Container := ⟨0, 0, 0, [], false⟩

/-- `real_quota`: the free normal pages after `mem_init`. -/
def real_quota (kl kh : Nat) (mm : MMTable) (size : Nat) : Nat :=
  unused_pages_AT (real_AT kl kh mm size (fun _ => .ATUndef)) (real_nps mm size - 1)

/-- `real_AC`: only the root container, with all free pages as its quota. -/
def real_AC (kl kh : Nat) (mm : MMTable) (size : Nat) : ContainerPool :=
  setAt (fun _ => Container_unused) 0 ⟨real_quota kl kh mm size, 0, 0, [], true⟩

/-- **`container_init_spec`**. -/
def container_init_spec (kl kh : Nat) (mm : MMTable) (size : Nat) (d : RData) : Option RData :=
  if d.init = false then
    some { d with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true,
                  AC := real_AC kl kh mm size }
  else none

theorem unused_congr {A B : ATable} : ∀ p, (∀ i, 0 < i → i ≤ p → A i = B i) →
    unused_pages_AT A p = unused_pages_AT B p
  | 0, _ => rfl
  | p + 1, h => by
    simp only [unused_pages_AT]
    rw [h (p + 1) (by omega) (Nat.le_refl _), unused_congr p (fun i h1 h2 => h i h1 (by omega))]

theorem unused_le (A : ATable) : ∀ p, unused_pages_AT A p ≤ p
  | 0 => Nat.le_refl _
  | p + 1 => by
    simp only [unused_pages_AT, pterm]
    have := unused_le A p
    split <;> omega

/-- `real_quota_unused_pages_AT`: the count does not depend on the table
`mem_init` started from. -/
theorem real_quota_unused {kl kh : Nat} {mm : MMTable} {size : Nat} (hkl : 0 < kl) (At : ATable) :
    unused_pages_AT (real_AT kl kh mm size At) (real_nps mm size - 1) = real_quota kl kh mm size := by
  unfold real_quota
  refine unused_congr _ (fun i h1 h2 => ?_)
  unfold real_AT
  rw [calAT_get kl kh _ mm size At hkl _ i h2, calAT_get kl kh _ mm size _ hkl _ i h2]

theorem real_AC_used {kl kh : Nat} {mm : MMTable} {size i : Nat}
    (h : (real_AC kl kh mm size i).cused = true) : i = 0 := by
  unfold real_AC at h
  by_cases e : i = 0
  · exact e
  · rw [setAt_ne _ _ e] at h; cases h

theorem real_AC_zero (kl kh : Nat) (mm : MMTable) (size : Nat) :
    real_AC kl kh mm size 0 = ⟨real_quota kl kh mm size, 0, 0, [], true⟩ := setAt_eq _ _ _

/-- **`real_AC` is a valid container pool.** -/
theorem real_container_valid {num_id mc kl kh : Nat} {mm : MMTable} {size : Nat} (hnum : 0 < num_id)
    (hq : real_quota kl kh mm size ≤ 2 ^ 32 - 1) : Container_valid num_id mc (real_AC kl kh mm size) := by
  constructor
  · intro i hi; rw [real_AC_used hi]; exact hnum
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]; exact hq
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]; exact Nat.zero_le _
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]; simp only; rw [real_AC_zero]
  · intro i hi j hj; have e := real_AC_used hi; subst e; rw [real_AC_zero] at hj; simp at hj
  · intro i hi h0; exact absurd (real_AC_used hi) h0
  · intro i hi j hj; have e := real_AC_used hi; subst e; rw [real_AC_zero] at hj; simp at hj
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]; exact .cqb_nil 0
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]; exact List.nodup_nil
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]; exact Nat.zero_le _
  · intro i hi; have e := real_AC_used hi; subst e; rw [real_AC_zero]; rfl
  · intro i hi j hj; have e := real_AC_used hi; subst e; rw [real_AC_zero] at hj; simp at hj

theorem real_AC_sum (kl kh : Nat) (mm : MMTable) (size : Nat) :
    ∀ n, sum_quotas (real_AC kl kh mm size) n = real_quota kl kh mm size
  | 0 => by simp [sum_quotas, real_AC_zero, qterm]
  | n + 1 => by
    simp only [sum_quotas]
    rw [real_AC_sum kl kh mm size n]
    have : qterm (real_AC kl kh mm size (n + 1)) = 0 := by
      unfold real_AC; rw [setAt_ne _ _ (by omega)]; rfl
    omega

/-- **`container_init_spec` establishes the invariants.** -/
theorem container_init_inv {maxpage num_id mc kl kh : Nat} {mm : MMTable} {size : Nat} {d d' : RData}
    (hkl : 0 < kl) (hsz : 0 < size) (hmax : 2 ^ 20 ≤ maxpage) (hnum : 0 < num_id) (hv : MM_valid mm size)
    (hk : MM_kern kl mm size) (hpp : d.pperm = fun _ => .PGUndef)
    (hs : container_init_spec kl kh mm size d = some d') :
    ATInv maxpage kl kh d'.toPData ∧ Container_valid num_id mc d'.AC ∧
    quota_bounded_AT num_id d'.AC d'.AT d'.nps := by
  unfold container_init_spec at hs
  by_cases hin : d.init = false
  · rw [if_pos hin] at hs
    simp only [Option.some.injEq] at hs; subst hs
    obtain ⟨h1, h2⟩ := real_nps_range hkl hsz hv hk
    have hql : real_quota kl kh mm size ≤ real_nps mm size - 1 := unused_le _ _
    refine ⟨?_, real_container_valid hnum (by omega), ?_⟩
    · have hm : mem_init_spec kl kh mm size d.toPData =
          some { d.toPData with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true } := by
        unfold mem_init_spec; rw [if_pos hin]
      exact mem_init_inv hkl hsz hmax hv hk hpp hm
    · show sum_quotas (real_AC kl kh mm size) (num_id - 1) ≤
        unused_pages_AT (real_AT kl kh mm size d.AT) (real_nps mm size - 1)
      rw [real_AC_sum, real_quota_unused hkl]; exact Nat.le_refl _
  · rw [if_neg hin] at hs; cases hs

end MContainer
