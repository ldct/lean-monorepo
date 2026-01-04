import Mathlib

-- Exercise 2.1.5
example {G : Type} [Group G] [Finite G] (H : Subgroup G)
: Nat.card H.carrier ≠ 0 := by sorry

instance {G : Type} [Group G] [Fintype G] (H : Subgroup G)
: Fintype H := sorry
