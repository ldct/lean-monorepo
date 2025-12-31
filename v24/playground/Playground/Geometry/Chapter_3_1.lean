import Mathlib

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

-- If φ is a homomorphism the fibers of φ are sets of G projecting to the same element in H
def MySetoid {G H} [Group G] [Group H] (φ : G →* H) : Setoid G := {
  r a b := φ a = φ b
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by
      intro x y z hxy hyz
      grind
    }
}



example {G H : Type*} [Group G] [Group H] (φ : G →* H)


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

example (g : Multiplicative (ZMod 3)) : (g^4 = g) := by
  fin_cases g <;> simp
  all_goals decide

example (g : DihedralGroup 3) : (g^7 = g) := by
  fin_cases g <;> simp
  all_goals decide

example (g : Q) : (g^9 = g) := by
  fin_cases g <;> simp
  all_goals decide


example : orderOf ((QuaternionGroup.a 1) : Q) = 4 := by
  rw [QuaternionGroup.orderOf_a_one]

#check QuotientGroup.fintype


theorem card_quot {G} [Group G] (N : Subgroup G) [N.Normal] (h : Nat.card N ≠ 0) :
  Nat.card (G ⧸ N) = (Nat.card G) / (Nat.card N) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  exact Nat.eq_div_of_mul_eq_left h rfl

theorem nat_card_ne_zero_of_fintype_nonempty {T} [Fintype T] [Nonempty T] : Nat.card T ≠ 0 := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_ne_zero



example : IsKleinFour (Q ⧸ (Subgroup.center Q)) := by
  constructor
  · rw [card_quot _ nat_card_ne_zero_of_fintype_nonempty]
    rw [ Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rfl
  · simp +decide [ Monoid.exponent ];
    split_ifs;
    · simp +decide only [Nat.find_eq_iff]

      native_decide
    · rename_i h;
      exact h <| by haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; exact
        Monoid.ExponentExists.of_finite;

-- Exercise 4. Interestingly the proof is just `rfl`.
set_option pp.coercions false in
theorem e4 {G} [Group G] (N : Subgroup G) [N.Normal] (g : G) (α : ℕ)
: (g : (G ⧸ N))^α = QuotientGroup.mk (g^α) := by
  rfl

example {G} [Group G] (N : Subgroup G) [N.Normal] (g : G) (h : IsOfFinOrder g)
: IsOfFinOrder (g : (G ⧸ N)) := by
  rw [isOfFinOrder_iff_pow_eq_one] at *
  obtain ⟨ n, hn, hn' ⟩ := h
  use n, hn
  rw [e4, hn']
  norm_cast
