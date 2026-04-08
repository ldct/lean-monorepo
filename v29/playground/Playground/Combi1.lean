import Mathlib

open Real
open scoped BigOperators

theorem my_favorite_theorem (k : ℕ) (hk : 1 ≤ k) :
  ∑' n : ℕ, (1 / Nat.choose (n + k + 1) n : ℝ) = 1 / k := by sorry
