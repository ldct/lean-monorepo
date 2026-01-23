import Mathlib

theorem exists_involution : ∃ r : DihedralGroup 4, r ≠ 1 ∧ r * r = 1 := by decide

theorem exists_involution' : ¬ ∃ r : Multiplicative (ZMod 7), r ≠ 1 ∧ r * r = 1 := by decide

noncomputable def extract
