import Mathlib


-- ℤ[x], the set of polynomials with integer coefficients, implemented as a function from ℕ to ℤ.
-- a₀ x⁰ + a₁ x¹ + a₂ x² + ... + aₙ xⁿ
@[ext]
structure MyPolynomial where
  coeffs : ℕ → ℤ
  support_deg : ℕ
  vanish : ∀ i, i > support_deg → coeffs i = 0

instance MyPolynomial.instAdd : Add MyPolynomial where
  add a b := {
    coeffs := fun i => a.coeffs i + b.coeffs i,
    support_deg := max a.support_deg b.support_deg,
    vanish := fun i hi => by
      have h1 : i > a.support_deg := by grind
      have h2 : i > b.support_deg := by grind
      simp [a.vanish i (by grind), b.vanish i (by grind)]
  }

lemma MyPolynomial.coeffs_add (a b : MyPolynomial) (i : ℕ)
: (a + b).coeffs i = a.coeffs i + b.coeffs i := rfl

lemma MyPolynomial.support_deg_add (a b : MyPolynomial)
: (a + b).support_deg = max a.support_deg b.support_deg := rfl

instance MyPolynomial.instZero : Zero MyPolynomial where
  zero := {
    coeffs := fun i => 0,
    support_deg := 0,
    vanish := fun i hi => by dsimp
  }

lemma MyPolynomial.coeffs_zero (i : ℕ)
: (0 : MyPolynomial).coeffs i = 0 := rfl

lemma MyPolynomial.support_deg_zero
: (0 : MyPolynomial).support_deg = 0 := rfl

instance MyPolynomial.instNeg : Neg MyPolynomial where
  neg a := {
    coeffs := fun i => -a.coeffs i,
    support_deg := a.support_deg,
    vanish := fun i hi => by
      simp [a.vanish i hi]
  }

instance MyPolynomial.instAddGroup : AddGroup MyPolynomial :=
  AddGroup.ofLeftAxioms (by
    intro a b c
    ext i
    · repeat rw [MyPolynomial.coeffs_add]
      ring
    · repeat rw [MyPolynomial.support_deg_add]
      grind only [= Nat.max_def, cases Or]
  ) (by
    intro a
    ext i
    · rw [MyPolynomial.coeffs_add, coeffs_zero]
      ring
    · rw [MyPolynomial.support_deg_add, support_deg_zero]
      grind only [= Nat.max_def]
  ) (by
    intro a
    ext i
    · rw [MyPolynomial.coeffs_add, coeffs_zero]
      ring
    · rw [MyPolynomial.support_deg_add, support_deg_zero]
      grind only [= Nat.max_def]
  )
