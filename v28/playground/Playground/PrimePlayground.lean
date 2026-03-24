import Mathlib

open Real Chebyshev Nat

namespace RS_prime_helper

lemma count_prime_le_imp_le_nth (m k : ℕ) (h : Nat.count Nat.Prime m ≤ k) :
    m ≤ Nat.nth Nat.Prime k := by
  by_contra hlt; push_neg at hlt
  have hp := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime k + 1) = k + 1 := by
    rw [Nat.count_succ, if_pos hp, Nat.count_nth_of_infinite Nat.infinite_setOf_prime]
  linarith [h1 ▸ Nat.count_monotone Nat.Prime hlt]
