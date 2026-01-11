import Mathlib

example (n : Nat) : (n * (n + 1)) % 2 = 0 := by
  exact Nat.mod_eq_zero_of_dvd (Nat.even_mul_succ_self n).two_dvd

example : 1 + 1 = 2 := by norm_num
