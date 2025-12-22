import Mathlib

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

def Group.IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

def Subgroup.IsAbelian {G} [Group G] (H : Subgroup G) : Prop := ∀ x ∈ H, ∀ y ∈ H, x * y = y * x


-- Exercise 3; every quotient of an abelian group is abelian
set_option pp.coercions false in
example {A} [Group A] (B : Subgroup A) [B.Normal] (h1 : Group.IsAbelian A)
: Group.IsAbelian (A ⧸ B) := by
  intro x y
  obtain ⟨ a, rfl ⟩ := QuotientGroup.mk_surjective x;
  obtain ⟨ b, rfl ⟩ := QuotientGroup.mk_surjective y;
  exact congr_arg _ ( h1 a b )

-- example from mm
abbrev Q := QuaternionGroup 2

example {G} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
  Nat.card (G ⧸ N) = (Nat.card G) / (Nat.card N) := by
  exact?


example : IsKleinFour (Q ⧸ (Subgroup.center Q)) := by
  constructor
  · rw [ Nat.card_eq_fintype_card ]
    have : Nat.card (Q ⧸ Subgroup.center Q) = (Nat.card Q) / (Fintype.card (Subgroup.center Q)) := by
      exact?
    rw [← @QuotientGroup.card_quotient_rightRel]
    native_decide
  · simp +decide [ Monoid.exponent ];
    split_ifs;
    · simp +decide only [Nat.find_eq_iff];
      native_decide +revert;
    · rename_i h;
      exact h <| by haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; exact
        Monoid.ExponentExists.of_finite;


set_option pp.coercions false in
example {G} [Group G] (N : Subgroup G) [N.Normal] (g : G) (α : ℕ)
: (g : (G ⧸ N))^α = QuotientGroup.mk (g^α) := by
  rfl
