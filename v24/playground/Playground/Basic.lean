import Mathlib

example (n : Nat) : (n * (n + 1)) % 2 = 0 := by
  fin_cases (n % 2) <;> norm_num

example : 1 + 1 = 2 := by norm_num
