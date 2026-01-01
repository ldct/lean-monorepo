import Mathlib

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

abbrev MAT:= Matrix (Fin 3) (Fin 3) ℝ

noncomputable def as_complex (M : MAT) : Matrix (Fin 3) (Fin 3) ℂ := (algebraMap ℝ ℂ).mapMatrix M

noncomputable def cpoly (g : SO3) := Matrix.charpoly (as_complex g.val)

lemma idlem (g : SO3) :  (cpoly g).roots.count 1 = 3 → g = 1 := by
  sorry
