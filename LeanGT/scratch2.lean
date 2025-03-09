import Mathlib
import LeanTeXMathlib

example (n : ℕ) (s : Finset ℕ)
: (∑ x ∈ s, 1) * n = (∑ x ∈ s, n) := by
  rw [Finset.sum_const]
  simp
