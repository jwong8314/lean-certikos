import CertiKOS.ClightToPyLive

/-!
# Fair runs of a C multicore machine terminate, given a certificate

A generic theorem about any multicore C machine (`CStepI P`). Take a
termination certificate (`ClightToPy.LiveCert`): a potential `Φ` that no step
raises, which every step of an *active* CPU lowers; other CPUs' steps keep a
CPU active; and some CPU is active while any is unfinished. Then every run in
which each unfinished CPU moves within every `K` steps has fewer than
`K * (Φ₀ + 1)` steps.

The argument: in each window of `K` steps, the CPU active at the window's
start stays active until it moves (`persist`). Fairness makes it move inside
the window, and that step lowers `Φ`.
-/

namespace FairC

open ClightL ClightToPy

variable {Pn Abs : Type}

/-- A finite run of the multicore machine `P`; at step `n`, CPU `lab n` moves. -/
structure GRun (P : Nat → Prims Pn Abs) where
  len : Nat
  cs : Nat → List (CThread Pn)
  ab : Nat → Abs
  lab : Nat → Nat
  step : ∀ n, n < len → CStepI P (lab n) (cs n) (ab n) (cs (n + 1)) (ab (n + 1))

variable {P : Nat → Prims Pn Abs}

/-- In every window of `K` steps, every unfinished CPU moves. -/
def GRun.Fair (r : GRun P) (K : Nat) : Prop :=
  ∀ n, n + K ≤ r.len → ∀ d (hd : d < (r.cs n).length), ¬ Done (r.cs n)[d] →
    ∃ j, n ≤ j ∧ j < n + K ∧ r.lab j = d

variable {G : List (CThread Pn) → Abs → Nat → Prop} {Act : List (CThread Pn) → Abs → Nat → Prop}

/-- Within one window, starting from an active CPU `d`: until `d` moves, `d` stays
active and `Φ` does not grow; once it has moved, `Φ` has dropped. -/
theorem window (C : LiveCert P G Act) (r : GRun P) {n K d Φn : Nat} (hG : G (r.cs n) (r.ab n) Φn)
    (hA : Act (r.cs n) (r.ab n) d) (hK : n + K ≤ r.len) :
    ∀ k, k ≤ K → ∃ Φ, G (r.cs (n + k)) (r.ab (n + k)) Φ ∧
      (Φ < Φn ∨ (Φ ≤ Φn ∧ Act (r.cs (n + k)) (r.ab (n + k)) d ∧ ∀ j, n ≤ j → j < n + k → r.lab j ≠ d)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨Φn, hG, .inr ⟨Nat.le_refl _, hA, fun j h1 h2 => by omega⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨Φ, hGk, hcase⟩ := ih (by omega)
    have hs := r.step (n + k) (by omega)
    rw [← Nat.add_assoc]
    rcases hcase with hlt | ⟨hle, hAk, hnot⟩
    · obtain ⟨Φ', h', hG'⟩ := C.le hGk hs
      exact ⟨Φ', hG', .inl (by omega)⟩
    · by_cases hl : r.lab (n + k) = d
      · rw [hl] at hs
        obtain ⟨Φ', h', hG'⟩ := C.lt hGk hAk hs
        exact ⟨Φ', hG', .inl (by omega)⟩
      · obtain ⟨Φ', h', hG'⟩ := C.le hGk hs
        refine ⟨Φ', hG', .inr ⟨by omega, C.persist hGk hAk hs hl, fun j h1 h2 => ?_⟩⟩
        by_cases hj : j = n + k
        · subst hj; exact hl
        · exact hnot j h1 (by omega)

theorem not_done_of_step (r : GRun P) {n : Nat} (hn : n < r.len) :
    ∃ i, ∃ hi : i < (r.cs n).length, ¬ Done (r.cs n)[i] := by
  obtain ⟨hi, c', hst, -, -⟩ := r.step n hn
  refine ⟨r.lab n, hi, fun hd => ?_⟩
  obtain ⟨h1, h2⟩ := hd
  have : ClightL.step (P (r.lab n)) ((r.cs n)[r.lab n].cfg (r.ab n)) = none :=
    step_final (by simp [CThread.cfg, Final, h1, h2])
  rw [this] at hst; cases hst

/-- **Fair runs terminate.** -/
theorem fair_terminates (C : LiveCert P G Act) (r : GRun P) {Φ₀ K : Nat} (hK : 0 < K)
    (h0 : G (r.cs 0) (r.ab 0) Φ₀) (hF : r.Fair K) : r.len < K * (Φ₀ + 1) := by
  -- after `m` full windows, the potential has dropped by `m`
  have hwin : ∀ m, m * K ≤ r.len → ∃ Φ, G (r.cs (m * K)) (r.ab (m * K)) Φ ∧ Φ + m ≤ Φ₀ := by
    intro m
    induction m with
    | zero => intro _; exact ⟨Φ₀, by simpa using h0, by omega⟩
    | succ m ih =>
      intro hm
      have hmK : m * K + K ≤ r.len := by rw [Nat.succ_mul] at hm; exact hm
      obtain ⟨Φ, hG, hΦ⟩ := ih (by omega)
      obtain ⟨i, hi, hnd⟩ := not_done_of_step r (n := m * K) (by omega)
      obtain ⟨d, hA⟩ := C.act hG ⟨i, hi, hnd⟩
      obtain ⟨hd, hnd'⟩ := C.act_lt hG hA
      obtain ⟨j, hj1, hj2, hj3⟩ := hF (m * K) hmK d hd hnd'
      obtain ⟨Φ', hG', hcase⟩ := window C r hG hA hmK K (Nat.le_refl _)
      rw [Nat.succ_mul]
      rcases hcase with hlt | ⟨-, -, hnot⟩
      · exact ⟨Φ', hG', by omega⟩
      · exact absurd hj3 (hnot j hj1 hj2)
  refine Nat.lt_of_not_le fun hle => ?_
  obtain ⟨Φ, -, hΦ⟩ := hwin (Φ₀ + 1) (by rw [Nat.mul_comm]; exact hle)
  omega

end FairC
