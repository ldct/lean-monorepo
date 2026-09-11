import Mathlib

example (x y : ℝ) (h : x < y) : (x + y) / 2 < y := by
  linarith

example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example : (∑ i ∈ Finset.range 10, i) = 45 := by
  norm_num
