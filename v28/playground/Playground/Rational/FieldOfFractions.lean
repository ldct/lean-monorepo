import Mathlib

/-
Construction of the field of fractions of an integral domain as a quotient type

https://mathweb.ucsd.edu/~jmckerna/Teaching/15-16/Spring/103B/l_14.pdf
-/

set_option linter.style.emptyLine false

namespace FieldOfFractions

attribute [grind <=] mul_right_cancel₀
attribute [grind .] Int.mul_ne_zero

structure PreFrac (R : Type*) [CommRing R] [IsDomain R]where
  num : R
  den : R
  nz : den ≠ 0

open Classical

/--
Definition-lemma 14.1
-/
instance PreFrac.instSetoid {R : Type*} [CommRing R] [IsDomain R] : Setoid (PreFrac R) where
  r a b := a.num * b.den = b.num * a.den
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by
      intro x y z hxy hyz
      have h : x.num * z.den * y.den = z.num * x.den * y.den := by
        grind
      grind [y.nz]
    }


theorem PreFrac.eq (R : Type*) [CommRing R] [IsDomain R] (a b c d : R) (hb : b ≠ 0) (hd : d ≠ 0)
: (⟨ a,b,hb ⟩ : PreFrac R) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

@[grind =]
theorem PreFrac.eq' (R : Type*) [CommRing R] [IsDomain R] (x y : PreFrac R) : x ≈ y ↔ x.num * y.den = x.den * y.num := by
  rw [PreFrac.eq]
  grind

@[grind]
def PreFracZero (R : Type*) [CommRing R] [IsDomain R] : PreFrac R := ⟨ 0, 1, one_ne_zero ⟩

theorem PreFracZero.equiv (R : Type*) [CommRing R] [IsDomain R] (a : PreFrac R) : a ≈ PreFracZero R ↔ a.num = 0 := by
  grind

/- 14.2 -/
def Frac (R : Type*) [CommRing R] [IsDomain R] := Quotient (@PreFrac.instSetoid R _ _)

noncomputable def Frac.formalDiv {R : Type*} [CommRing R] [IsDomain R] (a b : R) : Frac R :=
  Quotient.mk PreFrac.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, one_ne_zero ⟩)

lemma Frac.formalDiv_eq {R : Type*} [CommRing R] [IsDomain R] (a b : R) : formalDiv a b = Quotient.mk PreFrac.instSetoid (if h:b ≠ 0 then (⟨ a,b,h ⟩ : PreFrac R) else ⟨ 0, 1, one_ne_zero ⟩) := rfl

lemma Frac.formalDiv_eq' {R : Type*} [CommRing R] [IsDomain R] (a b : R) (hb : b ≠ 0) : formalDiv a b = Quotient.mk PreFrac.instSetoid  ⟨ a,b,hb ⟩ := by
  simp only [formalDiv_eq]
  rw [Quotient.eq]
  simp only [Setoid.r]
  grind

infix:100 " // " => Frac.formalDiv

@[grind =]
theorem Frac.eq {R : Type*} [CommRing R] [IsDomain R] (a c : R) {b d : R} (hb : b ≠ 0) (hd : d ≠ 0) : a // b = c // d ↔ a * d = c * b := by
  repeat rw [formalDiv_eq' _ _ (by grind)]
  rw [Quotient.eq]
  simp only [Setoid.r]

theorem Frac.eq_diff {R : Type*} [CommRing R] [IsDomain R] (n : Frac R) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quot.ind _ n
  intro ⟨ a, b, h ⟩
  use a, b; refine ⟨ h, ?_ ⟩
  simp [formalDiv, h]
  rfl

/-- Lemma 4.2.3 (Addition well-defined) -/
noncomputable instance Frac.add_inst {R : Type*} [CommRing R] [IsDomain R] : Add (Frac R) where
  add := Quotient.lift₂ (
    fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)
  ) (by
    intro ⟨ a, b, _ ⟩ ⟨ c, d, _ ⟩ ⟨ a', b', _ ⟩ ⟨ c', d', _ ⟩
    dsimp
    rw [formalDiv_eq' _ (b * d) (by (expose_names; exact (mul_ne_zero_iff_right nz_1).mpr nz))]
    rw [formalDiv_eq' _ (b' * d') (by (expose_names; exact (mul_ne_zero_iff_right nz_3).mpr nz_2))]
    rw [Quotient.eq]
    simp only [Setoid.r]
    grind
  )

/-- Definition 4.2.2 (Addition of rationals) -/
@[grind =]
theorem Frac.add_eq {R : Type*} [CommRing R] [IsDomain R] (a c : R) {b d : R} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

end FieldOfFractions
