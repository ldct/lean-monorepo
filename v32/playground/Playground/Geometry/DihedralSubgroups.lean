import Mathlib


namespace DihedralSubgroups

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

example (n : ℕ) (hn : 6 < n) (H : Subgroup (DihedralGroup n))
: IsDihedral H := by
  sorry


end DihedralSubgroups