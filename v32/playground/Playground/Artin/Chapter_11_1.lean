import Mathlib
import Playground.Artin.SqrtRing

variable {α : Type*}

namespace Artin

-- Definition 11.1.3
class CRing (R : Type*) extends AddCommGroup R, Mul R, Zero R, One R where
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
  add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c
  mul_comm : ∀ a b : R, a * b = b * a

instance : CRing ℂ where
  one_mul := by grind
  mul_one := by grind
  mul_assoc := by grind
  mul_add := by grind
  add_mul := by grind
  mul_comm := by grind

-- Definition 11.1.4 - polynomial ring. needs some thought.

-- Definition - the ring of continuous functions on the real line.

instance : CRing C(ℝ, ℝ) where
  one_mul := by grind
  mul_one := by grind
  mul_assoc := by grind
  mul_add := by grind
  add_mul := by grind
  mul_comm := by grind

namespace CRing

variable {R : Type*} [CRing R]

-- A lemma in Proposition 11.1.5
@[simp] lemma zero_mul (a : R) : 0 * a = 0 := by
  have : 0 * a = 0 * a := rfl
  nth_rw 1 [show (0 : R) = 0 + 0 by simp, add_mul] at this
  simp_all

@[simp] lemma mul_zero (a : R) : a * 0 = 0 := by
  have : a * 0 = a * 0 := rfl
  nth_rw 1 [show (0 : R) = 0 + 0 by simp, mul_add] at this
  simp_all

lemma neg_mul (a b : R) : (-a) * b = -(a * b) := by
  suffices h : a*b + (-a) * b = 0 by grind
  simp [← add_mul]

lemma mul_neg (a b : R) : a * (-b) = -(a * b) := by
  suffices h : a*b + a * (-b) = 0 by grind
  simp [← mul_add]

lemma neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg]
  simp

lemma neg_one_mul (a : R) : (-1 : R) * a = -a := by
  rw [neg_mul, one_mul]

@[ext] structure Subring (R : Type*) [CRing R] where
  carrier : Set R
  one_mem' : 1 ∈ carrier
  neg_mem' : ∀ x : R, x ∈ carrier → -x ∈ carrier
  add_mem' : ∀ x y : R, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  mul_mem' : ∀ x y : R, x ∈ carrier → y ∈ carrier → x * y ∈ carrier

instance : SetLike (Subring R) R where
  coe S := S.carrier
  coe_injective := by
    intro S T h
    ext x
    grind

namespace Subring

lemma one_mem (S : Subring R) : 1 ∈ S := S.one_mem'
lemma neg_mem (S : Subring R) (x : R) (h : x ∈ S) : -x ∈ S := S.neg_mem' x h
lemma add_mem (S : Subring R) (x y : R) (h₁ : x ∈ S) (h₂ : y ∈ S) : x + y ∈ S := S.add_mem' x y h₁ h₂
lemma mul_mem (S : Subring R) (x y : R) (h₁ : x ∈ S) (h₂ : y ∈ S) : x * y ∈ S := S.mul_mem' x y h₁ h₂
lemma sub_mem (S : Subring R) (z₁ z₂ : R) (h₁ : z₁ ∈ S) (h₂ : z₂ ∈ S) : z₁ - z₂ ∈ S := by
  rw [show z₁ - z₂ = z₁ + (-z₂) by grind]
  grind [Subring.add_mem, Subring.neg_mem]

lemma mem_carrier (x : R) (S : Subring R) :
  (x ∈ S) ↔ x ∈ S.carrier := by rfl

/- The intersection of a collection of subrings of a commutative ring is a subring -/
def IndexedIntersection
    {R} [CRing R] (𝒞 : Set (Subring R)) : Subring R where
  carrier := ⋂ (H ∈ 𝒞), H.carrier
  one_mem' := by simp [Set.mem_iInter, Subring.one_mem']
  neg_mem' := by grind [Set.mem_iInter, Subring.neg_mem']
  add_mem' := by grind [Set.mem_iInter, Subring.add_mem']
  mul_mem' := by grind [Set.mem_iInter, Subring.mul_mem']

@[simp, grind =] lemma mem_IndexedIntersection {𝒞 : Set (Subring R)} {x : R} :
    x ∈ IndexedIntersection 𝒞 ↔ ∀ H ∈ 𝒞, x ∈ H := by
  change x ∈ ⋂ (H ∈ 𝒞), H.carrier ↔
    ∀ H ∈ 𝒞, x ∈ H.carrier
  simp only [Set.mem_iInter]

/-
Definition 11.1.2 - the ring ℚ[c], as a subring of ℂ

The two defining properties of ℚ[c] are:
1. c ∈ ℚ[c]
2. ∀ q : ℚ, ↑q ∈ ℚ[c]

ℚ[c] is defined as the smallest subring that satisfies these two properties.
-/
def QAdjoin (c : ℂ) : Subring ℂ := IndexedIntersection { J | c ∈ J ∧ ∀ q : ℚ, ↑q ∈ J }
notation "ℚ[" c "]" => QAdjoin c

lemma QAdjoin.adjoin_mem (c : ℂ) : c ∈ ℚ[c] := by
  grind [QAdjoin, Set.mem_iInter]

lemma QAdjoin.rat_mem (q : ℚ) : ↑q ∈ ℚ[c] := by
  simp [QAdjoin]
  grind

example (z : ℝ) (q : ℚ) : z / q = z * (q⁻¹ : ℚ) := by
  norm_num
  field_simp

lemma helper (z : ℂ) (q : ℚ) : z / q = z * (q⁻¹ : ℚ) := by
  norm_num
  field_simp

lemma QAdjoin.divq_mem (z : ℂ) (q : ℚ) (h : z ∈ (ℚ[c])) : z / q ∈ (ℚ[c]) := by
  rw [helper]
  grind [Subring.mul_mem, rat_mem]

noncomputable abbrev γ : ℝ := √2 + √3

theorem QAdjoin.sqrt_6_mem : ↑√6 ∈ ℚ[γ] := by
  rw [show √6 = (γ ^ 2 - 5) / 2 by sqrt_ring]
  norm_num
  apply divq_mem
  apply Subring.sub_mem
  · rw [show ((√2 : ℂ) + √3) ^ 2 = (↑√2 + ↑√3) * (↑√2 + ↑√3) by field_simp]
    grind [Subring.mul_mem, adjoin_mem, rat_mem]
  apply rat_mem

/- Exercise 11.1.3 -/
theorem QAdjoin.sqrt_two_mem : ↑√2 ∈ ℚ[γ] := by
  have h1 :  ↑(√6 * (√2 + √3)) ∈ ℚ[γ] := by
    norm_num
    apply Subring.mul_mem
    · exact_mod_cast sqrt_6_mem
    norm_cast
    apply adjoin_mem
  rw [show √6 * (√2 + √3) = 2*√3 + 3*√2 by sqrt_ring] at h1
  have h2 : ↑(2*(√2 + √3)) ∈ ℚ[γ] := by
    norm_num
    apply Subring.mul_mem
    · apply rat_mem
    apply adjoin_mem
  have h3 : ↑(2 * √3 + 3 * √2 - (2 * (√2 + √3))) ∈ ℚ[γ] := by
    norm_cast
    have : ↑(2 * √3 + 3 * √2 - 2 * (√2 + √3)) = ((2 * √3 + 3 * √2) : ℂ) - (2 * (√2 + √3)) := by norm_num
    rw [this]
    apply Subring.sub_mem
    · push_cast at h1
      push_cast
      exact h1
    · push_cast at h2
      push_cast
      exact h2
  rw [show 2 * √3 + 3 * √2 - 2 * (√2 + √3) = √2 by linarith] at h3
  exact h3

def ZAdjoin (c : ℂ) : Subring ℂ := IndexedIntersection { J | c ∈ J }
notation "ℤ[" c "]" => ZAdjoin c

lemma ZAdjoin.adjoin_mem (c : ℂ) : c ∈ ℤ[c] := by
  grind [ZAdjoin, Set.mem_iInter]


end Subring

end CRing

end Artin
