import Mathlib

import Mathlib.Tactic

open Real

open Finset
open BigOperators

-- TODO: fix for v4.24 — `set_binom` and `esymm_pascal` are not available
-- def esymm (n : ℕ) (k : ℕ) (x : ℕ → ℝ): ℝ := ∑ A in set_binom n k, (∏ i in A, x i)
-- lemma newton_two ...
-- lemma esymm_one_eq_binom ...
