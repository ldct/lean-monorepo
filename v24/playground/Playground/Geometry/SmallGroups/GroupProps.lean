import Mathlib

def Group.IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

theorem Group.IsAbelian_iff {G} [Group G] : Group.IsAbelian G ↔ ∀ x y : G, x * y = y * x := by
  simp [Group.IsAbelian]

instance decidableGroupIsAbelian {G} [Group G] [Decidable (∀ g z : G, g * z = z * g)]
: Decidable (Group.IsAbelian G) :=
  decidable_of_iff' _ Group.IsAbelian_iff

def Group.FracInvolutions (G) [Group G] [Fintype G] [DecidableEq G] : ℚ :=
  (Finset.card { g : G | g^2 = 1} : ℚ) / (Fintype.card G : ℚ)

-- https://groupprops.subwiki.org/wiki/Commuting_fraction
def Group.CommutingFraction (G) [Group G] [Fintype G] [DecidableEq G] : ℚ :=
  (Finset.card { (g, h) : G × G | g * h = h * g} : ℚ) / (Fintype.card G : ℚ)^2
