import Mathlib

set_option linter.style.longLine false

/-
This file formalizes the definitions, theorems and exercises from Chapter 3.1 of Dummit and Foote (page 73).
-/

-- Mathlib already has a notion of quotient of a group by a normal subgroup. Much of Chapter 3.1 is devoted to constructing this quotient.
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

-- If φ is a homomorphism G → H the fibers of φ are sets of G projecting to the same element in H; hence two elements in G are related (written as `a ≃ b`) if they are mapped to the same element in H (written as `φ a = φ b`). This is an equivalence relation, and hence G partitions into equivalence classes.
@[to_additive AddHomSetoid] def HomSetoid {G H} [Group G] [Group H] (φ : G →* H) : Setoid G := {
  r a b := φ a = φ b
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by grind
    }
}

-- An element `g : HomFibers φ` is an equivalence class of elements in `G` under the equivalence relation `HomSetoid φ`.
@[to_additive AddHomFibers] abbrev HomFibers {G H} [Group G] [Group H] (φ : G →* H) : Type* := Quotient (HomSetoid φ)

-- Multiplication of the fibers is well-defined
@[to_additive] instance {G H} [Group G] [Group H] (φ : G →* H) : Mul (HomFibers φ) := ⟨
  Quotient.lift₂
    (fun x y => Quotient.mk (HomSetoid φ) (x * y))
    (by
      intro a₁ b₁ a₂ b₂ h₁ h₂
      simp [HomSetoid]
      change φ a₁ = φ a₂ at h₁
      change φ b₁ = φ b₂ at h₂
      congr
    )
⟩

@[to_additive] theorem mul_mk {G H} [Group G] [Group H] (φ : G →* H) (a b : G)
: Quotient.mk (HomSetoid φ) a * Quotient.mk (HomSetoid φ) b = Quotient.mk (HomSetoid φ) (a * b) := rfl

@[to_additive] instance {G H} [Group G] [Group H] (φ : G →* H) : One (HomFibers φ) := ⟨ Quotient.mk (HomSetoid φ) 1 ⟩

@[to_additive] instance {G H} [Group G] [Group H] (φ : G →* H) : Inv (HomFibers φ) := ⟨ Quotient.lift (fun x => Quotient.mk (HomSetoid φ) (x⁻¹)) (by
  intro a b h
  simp [HomSetoid]
  change φ a = φ b at h
  rw [h]
) ⟩

@[to_additive] theorem inv_mk {G H} [Group G] [Group H] (φ : G →* H) (a : G)
: (Quotient.mk (HomSetoid φ) a)⁻¹ = Quotient.mk (HomSetoid φ) (a⁻¹) := rfl

-- Group structure on the fibers
@[to_additive] instance {G H} [Group G] [Group H] (φ : G →* H) : Group (HomFibers φ) := {
  mul_assoc a b c := by
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    obtain ⟨ b, rfl ⟩ := Quotient.exists_rep b
    obtain ⟨ c, rfl ⟩ := Quotient.exists_rep c
    simp only [mul_mk]
    congr 1
    group
  one_mul a := by
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    rw [show (1 : HomFibers φ) = Quotient.mk (HomSetoid φ) 1 by exact rfl]
    simp only [mul_mk]
    congr 1
    group
  mul_one a := by
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    rw [show (1 : HomFibers φ) = Quotient.mk (HomSetoid φ) 1 by exact rfl]
    simp only [mul_mk]
    congr 1
    group
  inv_mul_cancel a := by
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    simp [inv_mk, mul_mk, show (1 : HomFibers φ) = Quotient.mk (HomSetoid φ) 1 by exact rfl]
}

/-
Example (page 74)
-/

def ClassOf {G H} [AddGroup G] [AddGroup H] (φ : G →+ H) (x : G) :=
  { y : G | φ y = φ x }

abbrev φ : ℤ →+ ZMod 2 := {
  toFun := fun n => (n : ZMod 2)
  map_zero' := by
    norm_num
  map_add' x y := by
    norm_num
  }

abbrev ZQuot2 := AddHomFibers φ
abbrev ZQuot2.mk := Quotient.mk (AddHomSetoid φ)

example (n : ℕ) : (n : ZMod 2) = 0 ↔ 2 ∣ n := by
  exact ZMod.natCast_eq_zero_iff n 2

example (n : ℤ) : (n : ZMod 2) = 0 ↔ 2 ∣ n := by
  grind [ZMod.intCast_zmod_eq_zero_iff_dvd]

example : ClassOf φ 0 = { n : ℤ | n % 2 = 0 } := by
  rw [Set.ext_iff]
  intro x
  simp [ClassOf]
  grind [ZMod.intCast_zmod_eq_zero_iff_dvd]

#check { n : ℤ | ZQuot2.mk n = ZQuot2.mk 0 }
#check ZQuot2.mk 3

/-
Definition (page 75)
-/

def Kernel (G H) [Group G] [Group H] (φ : G →* H) : Subgroup G := {
  carrier := { x : G | φ x = 1 }
  mul_mem' := by
    intro a b ha hb
    simp_all
  one_mem' := by
    simp
  inv_mem' := by
    simp
}

#check φ.ker

example : ZQuot2.mk 3 = ZQuot2.mk 1 := by
  simp [ZQuot2.mk, AddHomSetoid]
  decide


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

-- example from Visual Algebra: the Quaternion Group quotient by its center is the Klein Four Group
abbrev Q := QuaternionGroup 2

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
    simp [ Nat.card_eq_fintype_card ]
    rw [show Fintype.card (Subgroup.center Q) = 2 by rfl, show Fintype.card Q = 8 by rfl]
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
