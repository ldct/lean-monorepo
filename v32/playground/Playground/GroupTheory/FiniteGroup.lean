import Mathlib

variable {α : Type*}

namespace FiniteGroup

/-
Definition 1.2 - Abstract Group
-/
class Group (G : Type*) [DecidableEq G] extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

attribute [simp] Group.one_mul Group.mul_one Group.inv_mul_cancel Group.mul_inv_cancel



end FiniteGroup
