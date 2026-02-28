import Mathlib

variable {n : ℕ}

theorem neg_1_eq_n_minus_1 : ((-1 : ZMod n) = n-1) := by
  simp only [CharP.cast_eq_zero, zero_sub]

example (a : ZMod n) (b : ZMod n) (h : a = b) : a.val = b.val := by
  exact congrArg ZMod.val h
