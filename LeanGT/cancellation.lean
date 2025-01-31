import Mathlib

example (a b k : ℕ) (k_pos : k ≠ 0) (eq : k*a = k*b) : a = b := by
  exact (Nat.mul_right_inj k_pos).mp eq

example (a b k : ℝ) (k_pos : k ≠ 0) (eq : k*a = k*b) : a = b := by
  exact mul_left_cancel₀ k_pos eq