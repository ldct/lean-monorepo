import Mathlib

variable {α : Type*}

-- LOL this is actually dummit and foote

namespace Artin

--
class Ring (R : Type*) extends AddCommGroup R, Mul R, Zero R, One R where
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
  add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c

class CRing (R : Type*) extends Ring R where
  mul_comm : ∀ a b : R, a * b = b * a

class Field (F : Type*) extends CRing F, Inv F where
  inv_zero : (0 : F)⁻¹ = 0
  inv_mul_cancel : ∀ a : F, a ≠ 0 → a⁻¹ * a = 1


lemma Field.mul_inv_cancel {F : Type*} [Field F] (a : F) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  have := inv_mul_cancel a h
  grind [CRing.mul_comm]

namespace Ring

variable {R : Type*} [Ring R]

-- Proposition 7.1.1.1
@[simp] lemma zero_mul (a : R) : 0 * a = 0 := by
  have : 0 * a = 0 * a := rfl
  nth_rw 1 [show (0 : R) = 0 + 0 by simp, add_mul] at this
  simp_all

-- Proposition 7.1.1.1
@[simp] lemma mul_zero (a : R) : a * 0 = 0 := by
  have : a * 0 = a * 0 := rfl
  nth_rw 1 [show (0 : R) = 0 + 0 by simp, mul_add] at this
  simp_all

-- Proposition 7.1.1.2
lemma neg_mul (a b : R) : (-a) * b = -(a * b) := by
  suffices h : a*b + (-a) * b = 0 by grind
  simp [← add_mul]

-- Proposition 7.1.1.2
lemma mul_neg (a b : R) : a * (-b) = -(a * b) := by
  suffices h : a*b + a * (-b) = 0 by grind
  simp [← mul_add]

-- Proposition 7.1.1.3
lemma neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg]
  simp

-- Proposition 7.1.1.4
lemma neg_one_mul (a : R) : (-1 : R) * a = -a := by
  rw [neg_mul, one_mul]

@[ext]
structure Unit (R : Type*) [Ring R] where
  val : R
  inv : R
  inv_mul_val : inv * val = 1
  mul_inv_val : val * inv = 1
attribute [simp] Unit.inv_mul_val Unit.mul_inv_val

instance : Inv (Unit R) where
  inv a := {
    val := a.inv,
    inv := a.val,
    inv_mul_val := a.mul_inv_val,
    mul_inv_val := a.inv_mul_val,
  }
lemma Unit.val_inv {R : Type*} [Ring R] (a : Unit R) : (a⁻¹).val = a.inv := rfl
lemma Unit.inv_inv {R : Type*} [Ring R] (a : Unit R) : (a⁻¹)⁻¹ = a := rfl

instance : Mul (Unit R) where
  mul a b := {
    val := a.val * b.val,
    inv := b.inv * a.inv,

    mul_inv_val := by
      rw [show a.val * b.val * (b.inv * a.inv) = a.val * (b.val * b.inv) * a.inv by sorry]
      simp [a.val_inv, b.val_inv],
    mul_inv_val := by sorry,
  }

structure ZeroDivisor (R : Type*) [Ring R] where
  val : R
  cofactor : R
  cofactor_mul_val : cofactor * val = 0
  val_mul_cofactor : val * cofactor = 0



end Ring

end Artin
