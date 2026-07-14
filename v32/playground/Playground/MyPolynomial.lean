import Mathlib


-- ℤ[x], the set of polynomials with integer coefficients, implemented as a function from ℕ to ℤ.
-- a₀ x⁰ + a₁ x¹ + a₂ x² + ... + aₙ xⁿ
@[ext]
structure MyPolynomial where
  coeffs : ℕ → ℤ
  vanish : ∃ n, ∀ i, i > n → coeffs i = 0

instance MyPolynomial.instAdd : Add MyPolynomial where
  add a b := {
    coeffs := fun i => a.coeffs i + b.coeffs i,
    vanish := by
      obtain ⟨ na, ha ⟩ := a.vanish
      obtain ⟨ nb, hb ⟩ := b.vanish
      use max na nb
      grind
  }

lemma MyPolynomial.coeffs_add (a b : MyPolynomial) (i : ℕ)
: (a + b).coeffs i = a.coeffs i + b.coeffs i := rfl

instance MyPolynomial.instZero : Zero MyPolynomial where
  zero := {
    coeffs i := 0,
    vanish := by use 0; grind
  }

lemma MyPolynomial.coeffs_zero (i : ℕ)
: (0 : MyPolynomial).coeffs i = 0 := rfl

instance MyPolynomial.instNeg : Neg MyPolynomial where
  neg a := {
    coeffs i := -a.coeffs i,
    vanish := by
      obtain ⟨ na, ha ⟩ := a.vanish
      use na
      grind
  }

instance MyPolynomial.instAddGroup : AddGroup MyPolynomial :=
  AddGroup.ofLeftAxioms (by
    intro a b c
    ext i
    repeat rw [MyPolynomial.coeffs_add]
    ring
  ) (by
    intro a
    ext i
    simp [MyPolynomial.coeffs_add, coeffs_zero]
  ) (by
    intro a
    ext i
    show (-a).coeffs i + a.coeffs i = 0
    unfold instNeg
    simp
  )
