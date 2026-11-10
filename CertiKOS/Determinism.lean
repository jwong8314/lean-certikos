import CertiKOS.ClightL

/-!
# Determinism: reaching a final state rules out divergence

This is the semantic core of CertiKOS's "downward simulation is enough"
argument (MCS-lock paper §4.6). The implementation is deterministic once ε is
fixed, so if a forward simulation shows the code *can* reach a final state,
then that is the *only* run, and the code cannot diverge.

Contrast with a partial-correctness refinement such as Clift's `corres`: it
only constrains runs that terminate, so it says nothing about code that spins
forever (see `TicketLock.lean`, section "Vacuity check").
-/

namespace ClightL

variable {Pn Abs : Type} {P : Prims Pn Abs}

/-- Run `n` steps. -/
def iter (P : Prims Pn Abs) : Nat → Config Pn Abs → Option (Config Pn Abs)
  | 0, c => some c
  | n + 1, c => (step P c).bind (iter P n)

/-- The (unique) execution from `c` never stops. -/
def Diverges (P : Prims Pn Abs) (c : Config Pn Abs) : Prop :=
  ∀ n, (iter P n c).isSome

theorem iter_add (n m : Nat) (c : Config Pn Abs) :
    iter P (n + m) c = (iter P n c).bind (iter P m) := by
  induction n generalizing c with
  | zero => simp [iter]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [iter]
    cases step P c with
    | none => rfl
    | some c' => simp [ih]

theorem star_iter {c c' : Config Pn Abs} (h : Star P c c') : ∃ n, iter P n c = some c' := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp [iter, hs, hn]⟩

/-- If the code can reach a final configuration, it does not diverge. -/
theorem not_diverges_of_star_final {c c' : Config Pn Abs}
    (h : Star P c c') (hf : Final c') : ¬ Diverges P c := by
  intro hdiv
  obtain ⟨n, hn⟩ := star_iter h
  have h1 := hdiv (n + 1)
  rw [iter_add, hn] at h1
  simp [iter, step_final hf] at h1

/-- Final configurations reachable from `c` are unique. -/
theorem final_unique {c c₁ c₂ : Config Pn Abs}
    (h₁ : Star P c c₁) (hf₁ : Final c₁) (h₂ : Star P c c₂) (hf₂ : Final c₂) : c₁ = c₂ := by
  induction h₁ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step hs _ => simp [step_final hf₁] at hs
  | step hs _ ih =>
    cases h₂ with
    | refl => simp [step_final hf₂] at hs
    | step hs' h' =>
      rw [hs] at hs'
      cases hs'
      exact ih hf₁ h'

end ClightL
