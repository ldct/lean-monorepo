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

-/
