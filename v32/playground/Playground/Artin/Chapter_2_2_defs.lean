import Mathlib

variable {α : Type*}

namespace Artin

class Group (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

attribute [simp] Group.one_mul Group.mul_one Group.inv_mul_cancel Group.mul_inv_cancel

/- Proposition 2.2.3 -/
lemma Group.left_cancel {G} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  have := congr(a⁻¹ * $h)
  rw [← mul_assoc, ← mul_assoc] at this
  simp_all

/- Proposition 2.2.3 -/
lemma Group.right_cancel {G} [Group G] (a b c : G) (h : b * a = c * a) : b = c := by
  have := congr($h * a⁻¹)
  rw [mul_assoc, mul_assoc] at this
  simp_all

/- Definition 2.2.9 -/
@[ext] structure Subgroup (G : Type*) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ x y : G, x ∈ carrier → y ∈ carrier → x * y ∈ carrier
  inv_mem : ∀ x : G, x ∈ carrier → x⁻¹ ∈ carrier

instance {G : Type*} [Group G] : CoeSort (Subgroup G) (Type _) where
  coe H := { x : G // x ∈ H.carrier }

end Artin
