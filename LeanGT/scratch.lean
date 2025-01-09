import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Nat Finset

example (hn : n > 2): fib (n+2) = fib n + fib (n+1) := by
  plausible

example : fib (n+2) = fib n + fib (n+1) := by
  exact fib_add_two

example (h : n > 1 ): fib (n) = fib (n-1) + fib (n-2) := by
  let n' := n - 2
  have h' : n = n' + 2 := by
    omega
  rw [h']
  simp
  have : n' ≥ 0 := by linarith
  -- conv =>
  --   rhs
  --   rw [add_comm]
  rw  (occs := [2] ) [add_comm]
  exact fib_add_two

example (m : ℕ) : fib (m + 2) * fib m - fib (m + 1) ^ 2 = (-1 : ℤ) ^ (m + 1) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [pow_add, pow_one]
    repeat rw [fib_add_two] at *
    push_cast at *
    linear_combination -(1 * ih)

example (h : n > 1 ): fib (n) = fib (n-1) + fib (n-2) := by
  plausible

example (h : n > 0 ): fib (n+3) = 2*fib (n+1) + fib (n) := by
  plausible

#eval choose 3 2

#check sum_range_choose
#check sum_range_choose_halfway

theorem test (n : ℕ) : (∑ m ∈ range (n + 1), n.choose m) = 2 ^ n := by
  -- plausible
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this


#eval fib 22
