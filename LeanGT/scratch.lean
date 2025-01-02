import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

open Nat

example : fib (n+2) = fib n + fib (n+1) := by
  exact fib_add_two

example (h : n > 1 ): fib (n) = fib (n-1) + fib (n-2) := by
  let n' := n - 2
  have h' : n = n' + 2 := by
    omega
  rw [h']
  simp
  sorry

example (m : ℕ) : fib (m + 2) * fib m - fib (m + 1) ^ 2 = (-1 : ℤ) ^ (m + 1) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [pow_add, pow_one]
    repeat rw [fib_add_two] at *
    push_cast at *
    linear_combination -(1 * ih)



#eval fib 22
