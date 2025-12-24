import Mathlib

def Group.IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

theorem Group.IsAbelian_iff {G} [Group G] : Group.IsAbelian G ↔ ∀ x y : G, x * y = y * x := by
  simp [Group.IsAbelian]

instance decidableGroupIsAbelian {G} [Group G]
  [Decidable (∀ g z : G, g * z = z * g)]
: Decidable (Group.IsAbelian G) :=
  decidable_of_iff' _ Group.IsAbelian_iff

def Group.FracInvolutions (G) [Group G] [Fintype G] [DecidableEq G] : ℚ :=
  (Finset.card { g : G | g^2 = 1} : ℚ) / (Fintype.card G : ℚ)

-- https://groupprops.subwiki.org/wiki/Commuting_fraction
def Group.CommutingFraction (G) [Group G] [Fintype G] [DecidableEq G] : ℚ :=
  (Finset.card { (g, h) : G × G | g * h = h * g} : ℚ) / (Fintype.card G : ℚ)^2

def MyIsSubgroup (G) [Group G] [Fintype G] (H : Finset G) : Prop :=
  1 ∈ H ∧ Fintype.card H ∣ Fintype.card G ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)

theorem MyIsSubgroup_iff {G} [Group G] [Fintype G] (H : Finset G)
: MyIsSubgroup G H ↔ 1 ∈ H ∧ Fintype.card H ∣ Fintype.card G ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) := by
  simp [MyIsSubgroup]

instance decidableMyIsSubgroup {G} [Group G] [Fintype G] (H : Finset G)
  [Decidable (1 ∈ H ∧ Fintype.card H ∣ Fintype.card G ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H))]
: Decidable (MyIsSubgroup G H) :=
  decidable_of_iff' _ (MyIsSubgroup_iff H)

def Group.numSubgroups (G) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
  if (Fintype.card G > 12) then 0 else Fintype.card {s : Finset G | MyIsSubgroup G s}
