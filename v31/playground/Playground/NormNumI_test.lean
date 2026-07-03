import Playground.NormNumI
import Mathlib

open Complex

example : (1:ℂ) = 1 + 0 * I := by norm_num1
example : (I:ℂ) = 0 + 1 * I := by norm_num1

example : (3 + 2 * I) * (3 + 2 * I) = 5 + 12 * I := by
  ring_nf
  norm_num
