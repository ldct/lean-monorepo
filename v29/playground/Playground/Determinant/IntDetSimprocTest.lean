import Playground.Determinant.IntDetSimproc

/-!
# Tests for `intDetSimproc`

Covers:
* 2×2, 3×3, 4×4, 8×8 matrices with various determinants.
* A matrix whose ℚ-LU has fractions (so `n_min > 1`).
* No-op cases: singular matrix, matrix needing a permutation.
-/

open IntDetSimproc

namespace IntDetSimprocTest

/-! ## Positive cases: simproc reduces `det A` to a literal. -/

private def M2a : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]
example : M2a.det = 1 := by simp only [M2a, intDetSimproc]

-- 2×2 with fractional ℚ-LU: Doolittle gives L₂₁ = 3/2 so n_min = 2.
private def M2b : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 3, 4]
example : M2b.det = 5 := by simp only [M2b, intDetSimproc]

-- det = -1: exercises sign handling.
private def M2c : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 3, 5]
example : M2c.det = -1 := by simp only [M2c, intDetSimproc]

private def M3a : Matrix (Fin 3) (Fin 3) ℤ := !![2, 1, 0; 1, 2, 1; 0, 1, 1]
example : M3a.det = 1 := by simp only [M3a, intDetSimproc]

-- Non-unit determinant to exercise the `n_min^n` cancellation path.
private def M3b : Matrix (Fin 3) (Fin 3) ℤ := !![3, 1, 2; 2, 1, 1; 1, 1, 2]
example : M3b.det = 2 := by simp only [M3b, intDetSimproc]

-- Cartan matrix A₄: tridiagonal, det = 5.
private def M4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 2,  1,  0,  0;
      1,  2,  1,  0;
      0,  1,  2,  1;
      0,  0,  1,  2]
example : M4.det = 5 := by simp only [M4, intDetSimproc]

/-- The E₈ root lattice Cartan matrix, `det = 1`. Matches
`Determinant1.E₈_det` but closes in one `simp` call here. -/
private def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

theorem E₈_det : E₈.det = 1 := by simp only [E₈, intDetSimproc]

/-! ## No-op cases: simproc returns `.continue`.

For these inputs `intDetSimproc` bails out; the goal is closed by other
means. Each test would fail-to-close if the simproc incorrectly claimed
a determinant value. -/

-- Singular matrix: `exactMinScaling` returns `none` because det = 0.
private def Sing : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 2, 4]
set_option linter.unusedSimpArgs false in
example : Sing.det = 0 := by
  simp only [Sing, intDetSimproc, Matrix.det_fin_two_of]; decide

-- Matrix whose ℚ-LU needs a permutation (first pivot is zero).
private def NeedsPerm : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
set_option linter.unusedSimpArgs false in
example : NeedsPerm.det = -1 := by
  simp only [NeedsPerm, intDetSimproc, Matrix.det_fin_two_of]; decide

end IntDetSimprocTest

-- Confirm the E₈ proof only uses the standard axioms — no `sorryAx`,
-- no `Lean.ofReduceBool`.
#print axioms IntDetSimprocTest.E₈_det
