import Mathlib

variable (n : ℕ)
#synth InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n))

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]
