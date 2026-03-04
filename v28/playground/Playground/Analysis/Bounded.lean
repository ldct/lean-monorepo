import Mathlib.Tactic

-- Definition 2.3.1: Bounded sequence

namespace Bounded

def Bounded (a : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ (∀ n, |a n| < M)

-- The sequence 1/x is bounded
example : Bounded (fun n ↦ 1/(n+1)) := by
  unfold Bounded
  use 2
  constructor
  norm_num
  intro n
  have : |1 / ((n : ℝ) + 1)| = 1 / ((n : ℝ) + 1) := by exact abs_eq_self.mpr (by positivity)
  rw [this]
  simp
  rw [inv_lt_iff_one_lt_mul₀ (by linarith)]
  linarith


end Bounded