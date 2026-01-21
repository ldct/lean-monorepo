import Mathlib
import Plausible

/-!
# Fibonacci sequence

This file explores which fibonacci identities can be proved in an "automated" way.
--/


#eval Nat.fib 0
#eval Nat.fib 1
#eval Nat.fib 2

#synth HPow ℤ ℕ ℤ
def fib (n : ℤ) : ℤ := match n with
| Int.ofNat n => Nat.fib n
| Int.negSucc n => (-1 : ℤ)^n * (Nat.fib (n + 1) : ℤ)

theorem fib_add_one (n : ℤ) : fib (n + 1) = fib n + fib (n - 1) := by
  plausible

theorem f1 (n : ℤ) : fib n = fib (n - 1 + 1) := by grind
theorem f2 (n : ℤ) : fib n = fib (n - 1) + fib (n - 2) := by
  grind [fib_add_one]

grind_pattern f1 => fib n
grind_pattern f2 => fib n

example (n : ℕ)
: fib n = 2 * fib (n - 4) + 3 * fib (n - 3):= by
  grind


-- Identity 1 (page 2) from Proofs that Really Count
example
  (n : ℕ)
: ∑ i ∈ Finset.range (n + 1), fib (i + 1) = fib (n + 3) - 1 := by
  induction n
  case zero =>
    norm_num [fib]
  case succ n IH =>
    rw [Finset.sum_range_succ, IH]
    grind

-- Identity 2
example
  (n : ℕ)
: ∑ i ∈ Finset.range (n + 1), fib (2*i + 1) = fib (2*n + 2) := by
  induction n
  case zero =>
    norm_num [fib]
  case succ n IH =>
    rw [Finset.sum_range_succ, IH]
    grind

-- Identity 3
example
  (n m : ℕ)
: fib (n + m + 1) = fib (n + 1) * fib (m + 1) + fib (n) * fib (m) := by
  induction' m using Nat.strong_induction_on with m' IH
  sorry


-- Identity 7 (page 6) from Proofs that Really Count
theorem three_mul_fib_n
  (n : ℕ)
: 3 * fib n = fib (n + 2) + fib (n - 2) := by
  grind

-- Uncounted Identity 3a
theorem five_mul_fib_n
  (n : ℕ)
: 5 * fib n = fib (n + 3) + fib (n - 1) + fib (n - 4) := by
  grind

-- Uncounted Identity 3b
theorem six_mul_fib_n
  (n : ℕ)
: 6 * fib n = fib (n + 3) + fib (n + 1) + fib (n - 4) := by
  grind

-- Uncounter Identity 3c
theorem seven_mul_fib_n
  (n : ℕ)
: 7 * fib n = fib (n + 4) + fib (n - 4) := by
  grind


-- Uncounter Identity 3d
theorem eight_mul_fib_n
  (n : ℕ)
: 8 * fib n = fib (n + 4) + fib n + fib (n - 4) := by
  grind

-- 3e
theorem nine_mul_fib_n
  (n : ℕ)
: 9 * fib n = fib (n + 4) + fib (n + 1) + fib (n - 2) + fib (n - 4) := by
  grind

-- Identity 8
theorem f_sq
  (n : ℕ)
: (fib (n + 1))^2 = (fib (n + 2)) * (fib n) + (-1)^n := by
  nth_rw 2 [f2]
  rw [show (n : ℤ) + 2 - 1 = n + 1 by ring]
  rw [show (n : ℤ) + 2 - 2 = n by ring]
  nth_rw 1 [f2]
  rw [show (n : ℤ) + 1 - 1 = n by ring]
  rw [show (n : ℤ) + 1 - 2 = n - 1 by ring]
  sorry

-- Identity 9
example
  (n : ℕ)
: ∑ k ∈ Finset.range (n + 1), fib (k + 1)^2 = fib (n + 1) * fib (n + 2) := by
  induction n
  case zero =>
    norm_num [fib]
  case succ n IH =>
    rw [Finset.sum_range_succ, IH]
    grind

-- Identity 12
example
  (n : ℕ)
: ∑ k ∈ Finset.range (n + 1), fib (2*k) = fib (2*n + 1) - 1 := by
  induction n
  case zero =>
    norm_num [fib]
  case succ n IH =>
    rw [Finset.sum_range_succ, IH]
    grind

-- Identity 13
example
  (n : ℕ)
: (fib (n + 1))^2 + (fib (n + 2))^2 = fib (2*n + 3) := by
  sorry


-- Identity 16 (page 13) from Proofs that Really Count
theorem two_mul_fib_n
  (n : ℕ)
: 2 * fib n = fib (n + 1) + fib (n - 2) := by
  grind


-- Identity 18 (page 13) from Proofs that Really Count
theorem four_mul_fib_n
  (n : ℕ)
: 4 * fib n = fib (n + 2) + fib n + fib (n - 2) := by
  grind
