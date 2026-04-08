/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- theorem my_favorite_theorem (k : ℕ) :
  ∑' n : ℕ+, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 / k
-/

import Mathlib


theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ)) := by
  sorry

open Real

open scoped BigOperators

theorem my_favorite_theorem (k : ℕ) :
  ∑' n : ℕ+, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 / k := by
    sorry -- Aristotle-generated proof broken by v4.22→v4.24 API changes