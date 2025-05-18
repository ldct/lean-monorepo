import Mathlib
import LeanTeXMathlib

import Mathlib.Tactic

open Real

open Finset
open BigOperators

def esymm (n : ℕ) (k : ℕ) (x : ℕ → ℝ): ℝ := ∑ A in set_binom n k, (∏ i in A, x i)

/-- The second Newton identity
∑ i in range n, (x i)^2 = (esymm n 1 x)^2 - 2 * (esymm n 2 x)
-/
lemma newton_two {n : ℕ} {x: ℕ → ℝ}: ∑ i in range n, (x i)^2 = (esymm n 1 x)^2 - 2 * (esymm n 2 x) := by
  texify
-- in principle this can be deduced from MvPolynomial.psum_eq_mul_esymm_sub_sum but I was too lazy to do so and just did a direct induction proof instead
  induction' n with m ih
  . simp
  rw [sum_range_succ, Nat.succ_eq_add_one, (show esymm (m+1) 1 x = esymm (m+1) (0+1) x by simp), (show esymm (m+1) 2 x = esymm (m+1) (1+1) x by simp), ih, esymm_pascal, esymm_pascal]
  simp; ring

lemma esymm_one_eq_binom (n k : ℕ) : esymm n k (fun _ ↦ 1) = Nat.choose n k := by
  simp [esymm, set_binom]
