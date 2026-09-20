module
import Mathlib


structure Subobject (G : Type*) where

structure K (G) extends Subobject G where
  h : toSubobject = toSubobject

variable (p : ℕ) (G : Type*) [Group G]


#check Subgroup.toSubgroup

structure Sylow' extends Subgroup G where
  isPGroup' : IsPGroup p toSubgroup


example (x y : ℝ) (h : x < y) : (x + y) / 2 < y := by
  linarith

example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example : (∑ i ∈ Finset.range 10, i) = 45 := by
  norm_num
