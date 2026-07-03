import Mathlib

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

-- An exceptional subgroup of SO(3) is a finite subgroup that is not cyclic or dihedral
def IsExceptional (H : Subgroup SO3) : Prop :=
  ¬ IsCyclic H ∧ ¬ IsDihedral H ∧ Nat.card H ≠ 0

example (H : Subgroup SO3) : IsExceptional H ∧ Nat.card H= 12 := by
  sorry

example (H : Subgroup SO3) : IsExceptional H ∧ Nat.card H = 24 := by
  sorry

example (H : Subgroup SO3) : IsExceptional H ∧ Nat.card H = 60 := by
  sorry

example (H : Subgroup SO3) (h : IsExceptional H) : Nat.card H = 12 ∨ Nat.card H = 24 ∨ Nat.card H = 60 := by
  sorry
