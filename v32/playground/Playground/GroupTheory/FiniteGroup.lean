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

structure BSubgroup (G : Type*) [DecidableEq G] [Group G] where
  carrier : Finset G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ x y : G, x ∈ carrier → y ∈ carrier → x * y ∈ carrier
  inv_mem : ∀ x : G, x ∈ carrier → x⁻¹ ∈ carrier


end FiniteGroup
