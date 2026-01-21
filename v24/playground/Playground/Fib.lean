import Mathlib
import Plausible

/-!
# Fibonacci sequence
--/

open Nat

-- def f n := fib (n + 1)

def Fibonacci := Nat.fib

-- Identity 1 (page 2) from Proofs that Really Count
example
  (n : ℕ)
: ∑ i ∈ Finset.range (n + 1), Fibonacci (i + 1) = Fibonacci (n + 3) - 1 := by
  unfold Fibonacci
  induction n
  case zero =>
    simp [Nat.fib]
  case succ n IH =>
    rw [Finset.sum_range_succ, IH]
    rw [show n + 1 + 2 + 1 = n + 4 by ring]
    rw [show fib (n + 4) = fib (n + 3) + fib (n + 2) by grind [fib_add_one]]
    ring_nf
    rw [show fib (3 + n) - 1 + fib (2 + n) = fib (2 + n) + (fib (3 + n) - 1) by ring]
    zify
    norm_num
    grind


theorem n_eq (n : ℕ) (h : 0 < n) : fib n = fib (n - 1 + 1) := by grind

grind_pattern n_eq => fib n
grind_pattern fib_add_one => fib n

-- Identity 16 (page 13) from Proofs that Really Count
theorem two_mul_fib_n
  (n : ℕ)
  (hn : 2 ≤ n)
: 2 * fib n = fib (n + 1) + fib (n - 2) := by
  rw [fib_add_one (by grind)]
  grind [fib_add_one]

theorem f1 (n : ℕ) : fib n = fib (n - 1 + 1) := by sorry
theorem f2 (n : ℕ) : fib n = fib (n - 1) + fib (n - 2) := by sorry

grind_pattern f1 => fib n
grind_pattern f2 => fib n

example (n : ℕ)
: fib n = 2 * fib (n - 4) + 3 * fib (n - 3):= by
  grind

theorem two_mul_fib_n'
  (n : ℕ)
  (hn : 2 ≤ n)
: 2 * fib n = fib (n + 1) + fib (n - 2) := by
  grind (ematch := 30)

-- Identity 7 (page 6) from Proofs that Really Count
theorem three_mul_fib_n
  (n : ℕ)
  (hn : 2 ≤ n)
: 3 * fib n = fib (n + 2) + fib (n - 2) := by
  rw [fib_add_one (by omega)]
  simp
  have := two_mul_fib_n n hn
  unfold Fibonacci at this
  omega

-- Identity 18 (page 13) from Proofs that Really Count
theorem four_mul_fib_n
  (n : ℕ)
  (hn : 2 ≤ n)
: 4 * fib n = fib (n + 2) + fib n + fib (n - 2) := by
  have := three_mul_fib_n n hn
  sorry

-- Uncounted Identity 3a
theorem five_mul_fib_n
  (n : ℕ)
  (hn : 4 ≤ n)
: 5 * fib n = fib (n + 3) +fib (n - 1) + fib (n - 4) := by
  repeat rw [fib_add_one (by omega)]
  simp
  rw [fib_add_one (by omega)]
  suffices : 2 * fib n = fib (n - 1) + fib (n - 1) + fib (n - 1) + fib (n - 4)
  · grind
  rw [show fib n = fib (n - 1 + 1) by grind]
  rw [fib_add_one (by grind)]
  rw [show fib (n - 1 - 1) = fib (n - 3 + 1) by grind]
  rw [fib_add_one (by grind)]
  rw [show n - 3 - 1 = n - 4 by grind]
  rw [mul_add, mul_add]
  suffices : fib (n - 4) + 2 * fib (n - 3) = fib (n - 1)
  · grind
  rw [show fib (n - 1) = fib (n - 2 + 1) by grind]
  rw [fib_add_one (by grind)]
  rw [show fib (n - 2) = fib (n - 3 + 1) by grind]
  grind [fib_add_one]



-- Identity 2
example
  (n : ℕ)
: ∑ i ∈ Finset.range (n + 1), fib (2*i + 1) = fib (2*n + 2) := by
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
