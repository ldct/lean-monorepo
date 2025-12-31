import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Init
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.OrderOfElement
import Init.Data.List.Nat.Pairwise

set_option linter.style.longLine false

def Group.IsAbelian (G) [Group G] [Fintype G] [DecidableEq G] : Bool := decide (∀ x y : G, x * y = y * x)

theorem Group.IsAbelian_iff {G} [Group G] [Fintype G] [DecidableEq G] : Group.IsAbelian G ↔ ∀ x y : G, x * y = y * x := by
  simp [Group.IsAbelian]

-- instance decidableGroupIsAbelian {G} [Group G]
--   [Decidable (∀ g z : G, g * z = z * g)]
-- : Decidable (Group.IsAbelian G) :=
--   decidable_of_iff' _ Group.IsAbelian_iff

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
  if (Fintype.card G > 10) then 0 else Fintype.card {s : Finset G | MyIsSubgroup G s}


def finOrderOf {G} [Group G] [Fintype G] [DecidableEq G] (a : G) : Fin ((Fintype.card G) + 1):=
  Finset.min' { n : Fin ((Fintype.card G) + 1) | n ≠ 0 ∧ a ^ (n.val) = 1 } (by
    use ⟨ Fintype.card G, by grind ⟩
    simp
  )

def finOrderOf' {G} [Group G] [Fintype G] [DecidableEq G] (a : G) : Fin ((Fintype.card G) + 1):=
  Finset.min' { n : Fin ((Fintype.card G) + 1) | n ≠ 0 ∧ n.val ∣ (Fintype.card G) ∧ a ^ (n.val) = 1 } (by
    use ⟨ Fintype.card G, by grind ⟩
    simp
  )

-- theorem orderOf_eq {G} [Group G] [Fintype G] [DecidableEq G] (g : G)
-- : finOrderOf g = orderOf g := by
--   have h_finOrderOf_def : finOrderOf g = ⟨orderOf g, by
--     exact Nat.lt_succ_of_le ( orderOf_le_card_univ )⟩ := by
--     refine le_antisymm ?_ ?_;
--     · refine Finset.min'_le _ _ ?_
--       simp +decide [ pow_orderOf_eq_one ];
--       exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ orderOf g, orderOf_pos g, pow_orderOf_eq_one g ⟩;
--     · unfold finOrderOf
--       simp [ Finset.min' ]
--       intro b hb hb'
--       exact Nat.le_of_dvd ( Fin.pos_iff_ne_zero.2 hb ) ( orderOf_dvd_iff_pow_eq_one.2 hb' )
--   exact congr_arg Fin.val h_finOrderOf_def

theorem orderOf1 {G} [Group G] [Fintype G] [DecidableEq G] : finOrderOf' (1 : G) = 1 := by
  simp [finOrderOf']
  rw [Finset.min'_eq_iff]
  constructor
  · simp [Fintype.card_pos]
  rintro b hb
  simp at *
  obtain ⟨ hb1, hb2, hb3 ⟩ := hb
  exact Fin.one_le_of_ne_zero hb1

def Group.maxOrder' (G) [Group G] [Fintype G] [DecidableEq G] : Fin ((Fintype.card G) + 1) :=
  Finset.max' ( Finset.image (fun (g : G) ↦ finOrderOf' g) (Finset.univ : Finset G)) (by
    use ⟨ 1, by grind [Fintype.card_pos] ⟩
    simp
    use 1
    convert orderOf1
    simp
    rw [Nat.mod_eq_of_lt]
    grind [Fintype.card_pos]
  )

def Group.maxOrder (G) [Group G] [Fintype G] [DecidableEq G] : Nat :=
  (maxOrder' G).val
