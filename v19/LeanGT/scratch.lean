import Mathlib
import LeanTeXMathlib

theorem add_gt_add_right {a b:ℤ} (c:ℤ) (h: a > b) : a+c > b+c := by
  exact Int.add_lt_add_right h c
  linarith
