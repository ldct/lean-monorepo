/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- example
  (k : ℕ) (b : ℕ → ℝ)
:  ∑ x ∈ Finset.range (2 ^ (k + 2) - 1), b (x + 1)
  = ∑ x ∈ Finset.range (2 ^ (k + 1) - 1), b (x + 1)
  + ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1)
-/

import Mathlib


example
  (k : ℕ) (b : ℕ → ℝ)
:  ∑ x ∈ Finset.range (2 ^ (k + 2) - 1), b (x + 1)
  = ∑ x ∈ Finset.range (2 ^ (k + 1) - 1), b (x + 1)
  + ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1)
:= by
  rw [ Finset.sum_range_add_sum_Ico _ ( by gcongr <;> norm_num ) ]