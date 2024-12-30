import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import LeanGT.ZMul

-- example : ¬ IsCyclic ((DihedralGroup 6) × (DihedralGroup 6)) := by
--   intro x
--   sorry



theorem test [Group G] (a b : G) (a_eq_b : a = b) :  a⁻¹ = b⁻¹ := by
  exact congrArg Inv.inv a_eq_b

theorem t [Group G] (h g : G) : h⁻¹ = g⁻¹ → h = g  := by
  intro x
  have := test h⁻¹ g⁻¹ x
  simp at this
  exact this

-- probably not what it seems
example : IsCyclic ((ZMod 2) × (ZMod 3)) := by
  use (1, 1)
  refine Function.HasRightInverse.surjective ?_

  sorry
