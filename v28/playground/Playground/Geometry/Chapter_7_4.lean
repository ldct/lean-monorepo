import Mathlib

/-
Through this section R is a ring with identity 1 ≠ 0.
-/

/-
# Proposition 9 (part 1)

Let I be an ideal of R. I = R ↔ I contains a unit
-/

example {R} [Ring R] (I : Ideal R)
: I = ⊤ ↔ (∃ u, IsUnit u ∧ u ∈ I) := by
  constructor
  · intro rfl
    use 1
    simp
  rintro ⟨ u, hu1, hu2 ⟩
  ext r
  simp only [Submodule.mem_top, iff_true]
  rw [isUnit_iff_exists] at hu1
  obtain ⟨ v, h1, h2 ⟩ := hu1
  rw [show r = r * (v * u) by simp [h2]]
  rw [show r * (v * u) = r * v * u by group]
  rw [show r * v * u = (r * v) • u by simp]
  apply Ideal.mul_mem_left
  exact hu2

#check Field

example {R} [CommSemiring R] [Nontrivial R] (hf : ¬IsField R) :
∃ (x : R) (_ : x ≠ 0), ¬IsUnit x := by exact Ring.exists_not_isUnit_of_not_isField hf

theorem isField_iff_forall_ne_zero_isUnit {R} [CommRing R] [Nontrivial R] :
    IsField R ↔ ∀ a : R, a ≠ 0 → IsUnit a := by
  sorry

/-
# Proposition 9 (part 2)

Assume R is commutative. Then R is a field ↔ its only ideals are 0 and R.
-/
