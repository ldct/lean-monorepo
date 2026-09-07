import Playground.Artin.Chapter_11_1

namespace Artin
namespace CRing

variable {R : Type*} [CRing R]

-- A computable and a non-coputable

-- Definition: unit
@[ext]
structure Unit (R : Type*) [CRing R] where
  val : R
  inv : R
  val_inv : val * inv = 1
  inv_val : inv * val = 1
attribute [simp] Unit.inv_val Unit.val_inv

lemma inv_unique {a b c : R} (h1 : a * b = 1) (h2 : a * c = 1) : b = c := by
  have h3 : b * a = 1 := by
    rwa [mul_comm]
  have h : a*b = a*c := by grind
  have := congr(b * $h)
  simp only [← mul_assoc, h3, one_mul] at this
  exact this

@[simp] lemma Unit.eq_of_val_eq (u1 u2 : Unit R) : (u1.val = u2.val) ↔ (u1 = u2) := by
  constructor
  · intro h
    ext
    · assumption
    apply CRing.inv_unique u1.val_inv
    grind [u2.val_inv]
  · grind

instance : Inv (Unit R) where
  inv a := {
    val := a.inv,
    inv := a.val,
    inv_val := a.val_inv,
    val_inv := a.inv_val,
  }
lemma Unit.val_inv' {R : Type*} [CRing R] (a : Unit R) : (a⁻¹).val = a.inv := rfl
lemma Unit.inv_inv' {R : Type*} [CRing R] (a : Unit R) : (a⁻¹)⁻¹ = a := rfl


-- Definition: unit
@[ext]
structure Unit' (R : Type*) [CRing R] where
  val : R
  exists_inv : ∃ inv : R, val * inv = 1 ∧ inv * val = 1

noncomputable abbrev Unit'.inv (r : Unit' R) := r.exists_inv.choose
noncomputable instance : Inv (Unit' R) where
  inv a := {
    val := a.inv,
    exists_inv := ⟨ a.val, by grind⟩
  }

end CRing
end Artin
