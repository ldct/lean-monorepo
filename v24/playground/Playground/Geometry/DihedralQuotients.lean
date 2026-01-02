import Mathlib

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

example (n : ℕ) (hn : 6 < n) (H : Subgroup (DihedralGroup n)) (hg : Subgroup.Normal H)
: IsDihedral (DihedralGroup n ⧸ H) := by
  sorry
