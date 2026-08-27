import Playground.Artin.Chapter_11_1

variable {R : Type*} [CommRing R] in
#synth Mul (FormalSeries R)

namespace Artin

variable {R : Type*} [CRing R]

@[ext]
structure FormalSeries (R : Type u) [CRing R] where
  coeffs : ℕ → R

instance : Add (FormalSeries R) where
  add f g := ⟨fun n => f.coeffs n + g.coeffs n⟩
lemma add_coeffs (f g : FormalSeries R) (n : ℕ) : (f + g).coeffs n = f.coeffs n + g.coeffs n := rfl

instance : Zero (FormalSeries R) where
  zero := ⟨fun _ => 0⟩
lemma zero_coeffs (n : ℕ) : (0 : FormalSeries R).coeffs n = 0 := rfl

instance : Neg (FormalSeries R) where
  neg f := ⟨fun n => -f.coeffs n⟩
lemma neg_coeffs (f : FormalSeries R) (n : ℕ) : (-f).coeffs n = -f.coeffs n := rfl

instance : One (FormalSeries R) where
  one := ⟨fun _ => 1⟩
lemma one_coeffs (n : ℕ) : (1 : FormalSeries R).coeffs n = 1 := rfl

instance : Mul (FormalSeries R) where
  mul f g := ⟨fun n => ∑ p ∈ Finset.antidiagonal n, f.coeffs p.1 * g.coeffs p.2⟩
-- lemma coeffs_mul (f g : FormalSeries R) (n : ℕ) : (f * g).coeffs n = ∑ i : Finset.range (n + 1), f.coeffs i * g.coeffs (n - i) := rfl

instance : AddGroup (FormalSeries R) := .ofLeftAxioms
  (by
    intro f g h
    ext n
    grind [add_coeffs]
  )
  (by
    intro f
    ext n
    grind [zero_coeffs, add_coeffs]
  )
  (by
    intro f
    ext n
    grind [neg_coeffs, add_coeffs, zero_coeffs]
  )

instance : AddCommGroup (FormalSeries R) where
  add_comm f g := by
    ext n
    grind [add_coeffs]

instance : CRing (FormalSeries R) where
  one_mul := by
    intro f
    ext n
    simp only [mul_coeffs, one_coeffs, CRing.one_mul]
    sorry
  mul_one := by
    intro f
    ext n
    sorry
  mul_assoc := by sorry
  mul_add := by sorry
  add_mul := by sorry
  mul_comm := by sorry



end Artin
