import Mathlib

theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ)) := by
  field_simp [Nat.cast_choose];
  rw [ Nat.cast_choose ] <;> norm_num [ Nat.factorial, add_assoc ] ; ring;
  -- Let's simplify the expression by factoring out common terms.
  field_simp
  ring_nf at *

open Real
open scoped BigOperators

theorem my_favorite_theorem (k : ℕ) :
  ∑' n : ℕ+, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 / k := by
    -- Rewrite each term using `binom_inv_telescope`. The sum telescopes.
    sorry
