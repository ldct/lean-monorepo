import Mathlib
import LeanTeXMathlib

example (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, a (i + 1) = ∑ i ∈ Finset.Icc 1 n, a i := by
  rw [Finset.sum_bij (fun x _ ↦ x + 1)]
