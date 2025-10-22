import Mathlib

example
  (k : ℕ) (b : ℕ → ℝ)
:  ∑ x ∈ Finset.range (2 ^ (k + 2) - 1), b (x + 1)
  = ∑ x ∈ Finset.range (2 ^ (k + 1) - 1), b (x + 1)
  + ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1)
:= by
  rw [ Finset.sum_range_add_sum_Ico _ ( by gcongr <;> norm_num ) ]
