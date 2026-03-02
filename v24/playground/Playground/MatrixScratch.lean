import Mathlib

set_option linter.style.longLine false

abbrev castReal : ℤ →+* ℝ := Int.castRingHom ℝ

abbrev toReal (M : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ := M.map castReal

lemma toReal_mul (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    (A * B).map castReal = (A.map castReal) * (B.map castReal) := by
  simp_rw [Matrix.map_mul]
