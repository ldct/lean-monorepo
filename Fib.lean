import Mathlib
import LeanTeXMathlib
import Plausible

/-!
# Fibonacci sequence
--/

open Nat

def f n := fib (n + 1)

-- Identity 1
-- f0 + ... fn = f (n+2) - 1
example
  (n : ℕ)
: ∑ i ∈ Finset.range (n + 1), fib (i + 1) = fib (n + 3) - 1 := by
  induction n
  case zero =>
    simp [f]
    rw [show Nat.fib 3 = 2 by rfl]
  case succ n IH =>
    simp [f] at *
    rw [Finset.sum_range_succ, IH]
    rw [show n + 1 + 2 + 1 = n + 4 by ring]
    have : fib (n + 4) = fib (n + 3) + fib (n + 2) := by
      rw [fib_add_one, show n + 3 - 1 = n + 2 by rfl]
      ac_rfl
      positivity
    rw [this]
    ring_nf
    rw [show fib (3 + n) - 1 + fib (2 + n) = fib (2 + n) + (fib (3 + n) - 1) by ring]
    zify


    rw [cast_pred (by simp)]
    rw [cast_pred (by simp)]
    rw [cast_add]
    ring

-- Identity 2
example
  (n : ℕ)
: ∑ i ∈ Finset.range (n + 1), f (2*i) = f (2*n + 1) := by
  induction n
  case zero =>
    simp [f]
  case succ n IH =>
    simp [f] at *
    rw [Finset.sum_range_succ, IH]
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    rw [show fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) by
      rw [fib_add_one, show 2 * n + 2 - 1 = 2 * n + 1 by rfl]
      ac_rfl
      positivity
    ]
    ring_nf
    rw [show 4 + n*2 = 2*n + 4 by ring]
    have : 0 < 2 * n + 3 := by positivity
    rw [fib_add_one (by omega)]
    simp
    have : 0 < 2*n+2 := by positivity
    rw [fib_add_one (show 2*n+2 ≠ 0 by omega)]
    simp
    ring_nf

-- Example 16
theorem two_mul_fib_n
  (n : ℕ)
  (hn : 2 ≤ n)
: 2 * fib n = fib (n + 1) + fib (n - 2) := by
  rw [fib_add_one (by omega)]
  suffices : fib n = fib (n - 1) + fib (n - 2)
  omega
  rw [show fib n = fib (n - 1 + 1) by congr; omega]
  rw [fib_add_one (by omega)]
  rw [show n - 1 - 1 = n - 2 by omega]
  ac_rfl

-- Identity 7
theorem three_mul_fib_n
  (n : ℕ)
  (hn : 2 ≤ n)
: 3 * fib n = fib (n + 2) + fib (n - 2) := by
  rw [fib_add_one (by omega)]
  simp
  suffices : 2 * fib n = fib (n + 1) + fib (n - 2)
  omega
  exact two_mul_fib_n n hn

-- Identity 18
theorem four_mul_fib_n
  (n : ℕ)
  (hn : 2 ≤ n)
: 4 * fib n = fib (n + 2) +fib n + fib (n - 2) := by
  have := three_mul_fib_n n hn
  omega

-- Uncounted Identity 3a
theorem five_mul_fib_n
  (n : ℕ)
  (hn : 4 ≤ n)
: 5 * fib n = fib (n + 3) +fib (n - 1) + fib (n - 4) := by
  repeat rw [fib_add_one (by omega)]
  simp
  rw [fib_add_one (by omega)]
  suffices : 2 * fib n = fib (n - 1) + fib (n - 1) + fib (n - 1) + fib (n - 4)
  omega
  rw [show fib n = fib (n - 1 + 1) by congr; omega]
  rw [fib_add_one (by omega)]
  rw [show fib (n - 1 - 1) = fib (n - 3 + 1) by congr; omega]
  rw [fib_add_one (by omega)]
  rw [show n - 3 - 1 = n - 4 by omega]
  rw [mul_add, mul_add]
  suffices : fib (n - 4) + 2 * fib (n - 3) = fib (n - 1)
  omega
  rw [show fib (n - 1) = fib (n - 2 + 1) by congr; omega]
  rw [fib_add_one (by omega)]
  rw [show n - 2 - 1 = n - 3 by omega]
  rw [show fib (n - 2) = fib (n - 3 + 1) by congr; omega]
  rw [fib_add_one (by omega)]
  rw [show n - 3 - 1 = n - 4 by omega]
  omega
