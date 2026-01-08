import Mathlib

set_option linter.style.longLine false

/-
This file formalizes the definitions, theorems and exercises from Chapter 1.1 of Dummit and Foote (page 16).
-/

class MyGroup (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

class MyAddGroup (G : Type*) extends Add G, Zero G, Neg G where
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
  zero_add : ∀ a : G, 0 + a = a
  add_zero : ∀ a : G, a + 0 = a
  neg_add_cancel : ∀ a : G, a + (-a) = 0
  add_neg_cancel : ∀ a : G, (-a) + a = 0

instance : MyAddGroup ℚ where
  add_assoc a b c := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind
  add_neg_cancel := by grind

instance : MyAddGroup ℝ where
  add_assoc a b c := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind
  add_neg_cancel := by grind

instance : MyAddGroup ℂ where
  add_assoc a b c := by grind
  zero_add := by grind
  add_zero := by grind
  neg_add_cancel := by grind
  add_neg_cancel := by grind

/-
Example 6
-/
instance {A B} [MyGroup A] [MyGroup B] : Mul (A × B) := {
  mul := fun a b ↦ (a.1 * b.1, a.2 * b.2)
}

lemma MyGroup.prod_mul {A B} [MyGroup A] [MyGroup B] (a b : A × B) : a * b = (a.1 * b.1, a.2 * b.2) := rfl

instance {A B} [MyGroup A] [MyGroup B] : One (A × B) := {
  one := (1, 1)
}

instance {A B} [MyGroup A] [MyGroup B] : MyGroup (A × B) where
  mul_assoc := by
    rintro ⟨ a₁, a₂ ⟩ ⟨ b₁, b₂ ⟩ ⟨ c₁, c₂ ⟩
    simp [MyGroup.prod_mul]
    constructor
    · exact MyGroup.mul_assoc a₁ b₁ c₁
    · exact MyGroup.mul_assoc a₂ b₂ c₂
  one_mul := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.one_mul]
  mul_one := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.mul_one]
  inv_mul_cancel := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.inv_mul_cancel]
  mul_inv_cancel := by
    rintro ⟨ a, b ⟩
    simp [MyGroup.prod_mul, MyGroup.mul_inv_cancel]

/-
Proposition 1.1

The identity is unique. We formulate this as: there is a unique element `e` such that `IsNeutralElement e` holds.
`∃!x, P x` is syntactic sugar for `∃ x, P x ∧ ∀ y, P y → y = x`.
-/

def MyGroup.IsNeutralElement {G} [MyGroup G] (e : G) : Prop := ∀ a : G, e * a = a ∧ a * e = a

lemma MyGroup.IsNeutralElement.unique {G} [MyGroup G] : ∃! e : G, IsNeutralElement e := by
  use 1
  constructor
  · intro a
    simp [MyGroup.one_mul, MyGroup.mul_one]
  · intro y hy
    have := hy 1
    grind [MyGroup.one_mul]

/-
Proposition 1.2

The inverse is unique. We formulate this as: for every element `a`, we have ∃! b, AreInverse a b
-/

def MyGroup.AreInverse {G} [MyGroup G] (a b : G) : Prop := a * b = 1 ∧ b * a = 1

lemma MyGroup.AreInverse.right_unique {G} [MyGroup G] (a b c : G) (hb : AreInverse a b) (hc : AreInverse a c) : c = b := by
  calc
    c = c * 1 := by simp [MyGroup.mul_one]
    _ = c * (a * b) := by (congr 1; rw [hb.1])
    _ = (c * a) * b := by rw [MyGroup.mul_assoc]
    _ = 1 * b := by (congr 1; rw [hc.2])
    _ = b := by simp [MyGroup.one_mul]

lemma MyGroup.AreInverse.helper {G} [MyGroup G] (a : G) : AreInverse a a⁻¹ := by grind [AreInverse, MyGroup.inv_mul_cancel, MyGroup.mul_inv_cancel]

lemma MyGroup.AreInverse.right_unique_exists {G} [MyGroup G] (a : G) : ∃! b : G, AreInverse a b := by
  use a⁻¹
  have h' := helper a
  grind [right_unique]

lemma MyGroup.AreInverse.iff {G} [MyGroup G] (a b : G) : AreInverse a b ↔ a⁻¹ = b := by
  have h' := helper a
  grind [right_unique]

lemma MyGroup.AreInverse.symm {G} [MyGroup G] (a b : G) : AreInverse a b ↔ AreInverse b a := by grind [MyGroup.AreInverse]
lemma MyGroup.AreInverse.left_unique {G} [MyGroup G] (a b c : G) (hb : AreInverse b a) (hc : AreInverse c a) : b = c := by
  grind [MyGroup.AreInverse.symm, MyGroup.AreInverse.right_unique]

/-
Proposition 1.3
-/

lemma MyGroup.inv_inv {G} [MyGroup G] (a : G) : (a⁻¹)⁻¹ = a := by
  rw [← MyGroup.AreInverse.iff]
  grind [MyGroup.AreInverse.symm, MyGroup.AreInverse.helper]

/-
Proposition 1.4

We use an alternate proof, pulling forward some ideas from Poposition 2.
-/

lemma MyGroup.test2 {G} [MyGroup G] (a b : G) (h : a * b = 1) : (b * a = 1) := by
  have := congrArg (fun x => x * b⁻¹) h
  dsimp at this
  rw [mul_assoc, mul_inv_cancel, mul_one, one_mul] at this
  have := congrArg (fun x => x⁻¹) this
  dsimp at this
  rw [inv_inv] at this
  rw [← AreInverse.iff] at this
  exact this.2

theorem MyGroup.AreInverse.iff' {G} [MyGroup G] (a b : G) : AreInverse a b ↔ a * b = 1 := by
  constructor
  · intro h
    exact h.1
  · intro h
    have := test2 a b h
    grind [AreInverse]

example {G} [MyGroup G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← MyGroup.AreInverse.iff]
  rw [MyGroup.AreInverse.iff']
  rw [← MyGroup.mul_assoc, MyGroup.mul_assoc a b, MyGroup.mul_inv_cancel, MyGroup.mul_one, MyGroup.mul_inv_cancel]

/-
Cancellation laws
-/
lemma MyGroup.mul_left_cancel {G} [MyGroup G] (a u v : G) : a * u = a * v ↔ u = v := by
  constructor
  · intro h
    have := congrArg (fun x => a⁻¹ * x) h
    dsimp at this
    rwa [← MyGroup.mul_assoc, MyGroup.inv_mul_cancel, MyGroup.one_mul, ← MyGroup.mul_assoc, MyGroup.inv_mul_cancel, MyGroup.one_mul] at this
  · grind

lemma MyGroup.mul_right_cancel {G} [MyGroup G] (b u v : G) : u * b = v * b ↔ u = v := by
  constructor
  · intro h
    have := congrArg (fun x => x * b⁻¹) h
    dsimp at this
    rwa [MyGroup.mul_assoc, MyGroup.mul_inv_cancel, MyGroup.mul_one, MyGroup.mul_assoc, MyGroup.mul_inv_cancel, MyGroup.mul_one] at this
  · grind


/-
Exponentiation
-/
def MyGroup.npow {G} [MyGroup G] (g : G) (n : ℕ) : G :=
  match n with
  | 0 => 1
  | n + 1 => g * npow g n

instance {G} [MyGroup G] : Pow G ℕ := {
  pow := MyGroup.npow
}

lemma MyGroup.npow_zero {G} [MyGroup G] (g : G) : g ^ 0 = 1 := rfl
lemma MyGroup.npow_succ {G} [MyGroup G] (g : G) (n : ℕ) : g ^ (n + 1) = g * g ^ n := rfl

lemma MyGroup.npow_add {G} [MyGroup G] (g : G) (m n : ℕ) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n with
  | zero =>
    sorry
  | succ n IH =>
    sorry

def MyGroup.zpow {G} [MyGroup G] (g : G) (n : ℤ) : G :=
  match n with
  | Int.ofNat n => g ^ n
  | Int.negSucc n => (g ^ (n + 1))⁻¹

instance {G} [MyGroup G] : Pow G ℤ := {
  pow := MyGroup.zpow
}

lemma MyGroup.zpow_cast {G} [MyGroup G] (g : G) (n : ℕ) : g ^ (n : ℤ) = g ^ (n : ℕ) := by
  sorry

lemma MyGroup.zpow_add {G} [MyGroup G] (g : G) (m n : ℤ) : g ^ (m + n) = g ^ m * g ^ n := by
  sorry

lemma MyGroup.zpow_mul {G} [MyGroup G] (g : G) (m n : ℤ) : g ^ (m * n) = (g ^ m) ^ n := by
  sorry

lemma MyGroup.zpow_inv {G} [MyGroup G] (g : G) (n : ℤ) : g ^ (-n) = (g ^ n)⁻¹ := by
  sorry

lemma MyGroup.zpow_pow {G} [MyGroup G] (g : G) (m n : ℤ) : g ^ (m * n) = (g ^ m) ^ n := by
  sorry

lemma MyGroup.inv_zpow {G} [MyGroup G] (g : G) (n : ℤ) : (g⁻¹) ^ n = g ^ (-n) := by
  sorry

/-
Order
-/



-- def MyGroup.orderOf {G} [MyGroup G] (g : G) : ℕ :=
--   Nat.find (Set.min { n : ℕ | g ^ n = 1 } (by
--     use 0
--     simp
--   )

-- lemma MyGroup.orderOf_pos {G} [MyGroup G] (g : G) : MyGroup.orderOf g > 0 := by
--   simp [MyGroup.orderOf]
--   exact Finset.min'_pos _

-- lemma MyGroup.orderOf_dvd_of_pow_eq_one {G} [MyGroup G] (g : G) (n : ℕ) (h : g ^ n = 1) : MyGroup.orderOf g ∣ n := by
--   simp [MyGroup.orderOf]
--   exact Finset.min'_mem _
