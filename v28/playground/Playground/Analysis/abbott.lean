import Playground.Analysis.TendsTo

-- Exercise 2.2.7: Define convergence to infinity

namespace abbott
open TendsTo

def TendsToInf (a : ℕ → ℝ) : Prop :=
  ∀ M > 0, ∃ B : ℕ, ∀ n, B ≤ n → M < a n

theorem tendsToInf_def {a : ℕ → ℝ} :
    TendsToInf a ↔ ∀ M, 0 < M → ∃ B : ℕ, ∀ n, B ≤ n → M < a n := by
  rfl


-- a_n = sqrt n tends to infinity

example : TendsToInf (fun n ↦ Real.sqrt n) := by
  rw [tendsToInf_def] at *
  intro M M_pos

  use ⌈M * M⌉₊ + 1

  intro n n_large

  have n_large : ⌈M * M⌉₊ < n := by linarith

  rify at n_large
  have hB_sqrt := (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr n_large

  calc
    M = Real.sqrt (M^2) := by rw [Real.sqrt_sq (by positivity)]
    _ = Real.sqrt (M*M) := by ring_nf
    _ <= Real.sqrt ↑⌈M * M⌉₊ := by {
      simp only [Nat.cast_nonneg, Real.sqrt_le_sqrt_iff]
      exact Nat.le_ceil (M * M)
    }
    _ < Real.sqrt n := hB_sqrt


end abbott