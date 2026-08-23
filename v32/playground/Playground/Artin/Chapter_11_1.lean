import Mathlib

variable {α : Type*}

-- LOL this is actually dummit and foote

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

@[ext]
structure Unit (R : Type*) [CRing R] where
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
lemma Unit.val_inv {R : Type*} [CRing R] (a : Unit R) : (a⁻¹).val = a.inv := rfl
lemma Unit.inv_inv {R : Type*} [CRing R] (a : Unit R) : (a⁻¹)⁻¹ = a := rfl

@[ext] structure Subring (R : Type*) [CRing R] where
  carrier : Set R
  one_mem : 1 ∈ carrier
  neg_mem : ∀ x : R, x ∈ carrier → -x ∈ carrier
  add_mem : ∀ x y : R, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  mul_mem : ∀ x y : R, x ∈ carrier → y ∈ carrier → x * y ∈ carrier

instance : Membership R (Subring R) where
  mem J r := r ∈ J.carrier

/- The intersection of a collection of subrings of a commutative ring is a subring -/
def IndexedIntersection
    {R} [CRing R] (𝒞 : Set (Subring R)) : Subring R where
  carrier := ⋂ (H ∈ 𝒞), H.carrier
  one_mem := by simp [Set.mem_iInter, Subring.one_mem]
  neg_mem := by grind [Set.mem_iInter, Subring.neg_mem]
  add_mem := by grind [Set.mem_iInter, Subring.add_mem]
  mul_mem := by grind [Set.mem_iInter, Subring.mul_mem]

def containsRationals (J : Subring ℂ) : Prop := ∀ q : ℚ, ↑q ∈ J

def QAdjoin (c : ℂ) : Subring ℂ := IndexedIntersection { J | c ∈ J ∧ containsRationals J }

notation "ℚ[" c "]" => QAdjoin c

lemma QAdjoin.adjoin_mem (c : ℂ) : c ∈ (ℚ[c]) := by
  change c ∈ ℚ[c].carrier
  simp [QAdjoin, IndexedIntersection, Set.mem_iInter]
  intro J hJ _
  exact hJ

lemma QAdjoin.sum_mem (z₁ z₂ : ℂ) (h₁ : z₁ ∈ (ℚ[c]).carrier) (h₂ : z₂ ∈ (ℚ[c]).carrier) : z₁ + z₂ ∈ (ℚ[c]).carrier := by
  grind [QAdjoin, IndexedIntersection, Set.mem_iInter]

lemma QAdjoin.sum_mem' (z₁ z₂ : ℂ) (h₁ : z₁ ∈ (ℚ[c])) (h₂ : z₂ ∈ (ℚ[c])) : z₁ + z₂ ∈ (ℚ[c]) := by
  grind [QAdjoin, IndexedIntersection, Set.mem_iInter]







end CRing

end Artin
