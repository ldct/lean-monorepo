import Playground.RealIsometry.Basic

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

def IsExceptional (H : Subgroup RealIsometry) : Prop :=
  ¬ IsCyclic H ∧ ¬ IsDihedral H ∧ Nat.card H ≠ 0

theorem RealIsometry.existsExceptional (n : ℕ) [NeZero n]
: ∃ f : Subgroup RealIsometry, IsExceptional f := by
  sorry

theorem RealIsometry.existsExceptionalOfOrder12 (n : ℕ) [NeZero n]
: ∃ f : Subgroup RealIsometry, IsExceptional f ∧ Nat.card f = 12 := by
  sorry

theorem RealIsometry.existsExceptionalOfOrder24 (n : ℕ) [NeZero n]
: ∃ f : Subgroup RealIsometry, IsExceptional f ∧ Nat.card f = 24 := by
  sorry

theorem RealIsometry.existsExceptionalOfOrder60 (n : ℕ) [NeZero n]
: ∃ f : Subgroup RealIsometry, IsExceptional f ∧ Nat.card f = 60 := by
  sorry
