import Playground.RealIsometry


abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

theorem RealIsometry.isDihedral (n : ℕ) [NeZero n]
: ∃ f : Subgroup RealIsometry, IsDihedral f := by
  sorry
