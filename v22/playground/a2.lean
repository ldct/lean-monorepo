/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- example : 1 + 1 = 2

- theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ))
-/

import Mathlib


example : 1 + 1 = 2 := by
  -- Simplify the expression $1 + 1$ to $2$.
  norm_num

theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ)) := by
  field_simp [Nat.cast_choose];
  rw [ Nat.cast_choose ] <;> norm_num [ Nat.factorial, add_assoc ] ; ring;
  -- Let's simplify the expression by factoring out common terms.
  field_simp
  ring_nf at *