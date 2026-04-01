import Playground.Determinant2

/-!
# E₈ determinant via scaling to an integer matrix

We prove `E₈.det = 1` by first scaling to `60 • E₈` (an integer matrix
whose LU decomposition is entirely integral), then factoring as L * U
and computing determinants of the triangular factors.

The number 60 = n_min(E₈) is the minimal positive integer such
that `60 · E₈ = L · U` with integer L, U.
-/

open Matrix in
lemma det_of_smul_det {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ} {d : ℤ}
    (hk : k ≠ 0)
    (h : (k • M).det = k ^ n * d) :
    M.det = d := by
  rw [det_smul, Fintype.card_fin] at h
  exact mul_left_cancel₀ (pow_ne_zero n hk) h

def E₈_L : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  60,    0,    0,    0,    0,    0,    0,   0;
        0,   60,    0,    0,    0,    0,    0,   0;
      -30,    0,   30,    0,    0,    0,    0,   0;
        0,  -30,  -20,   10,    0,    0,    0,   0;
        0,    0,    0,  -12,   12,    0,    0,   0;
        0,    0,    0,    0,  -15,   15,    0,   0;
        0,    0,    0,    0,    0,  -20,   20,   0;
        0,    0,    0,    0,    0,    0,  -30,  30]

def E₈_U : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
      0,  0,  3, -2,  0,  0,  0,  0;
      0,  0,  0,  5, -6,  0,  0,  0;
      0,  0,  0,  0,  4, -5,  0,  0;
      0,  0,  0,  0,  0,  3, -4,  0;
      0,  0,  0,  0,  0,  0,  2, -3;
      0,  0,  0,  0,  0,  0,  0,  1]

set_option linter.flexible false in
lemma E₈_L_det : E₈_L.det = 116640000000 := by
  simp only [E₈_L]
  apply my_helper 2 0 (2:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 3 1 (2:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 3 2 (3:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 4 3 (5:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 5 4 (4:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 6 5 (3:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 7 6 (2:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  rw [Matrix.det_of_upperTriangular]
  · decide +kernel
  · unfold Matrix.BlockTriangular; decide +kernel

set_option linter.flexible false in
lemma E₈_U_det : E₈_U.det = 1440 := by
  simp only [E₈_U]
  rw [Matrix.det_of_upperTriangular]
  · decide +kernel
  · unfold Matrix.BlockTriangular; decide +kernel

lemma E₈_LU : 60 • E₈ = E₈_L * E₈_U := by
  simp only [E₈, E₈_L, E₈_U]
  decide +kernel

set_option linter.flexible false in
theorem E₈_det' : E₈.det = 1 := by
  apply det_of_smul_det (k := 60) (by decide)
  calc (60 • E₈).det
      = (E₈_L * E₈_U).det := by rw [E₈_LU]
    _ = E₈_L.det * E₈_U.det := Matrix.det_mul _ _
    _ = 60 ^ 8 * 1 := by rw [E₈_L_det, E₈_U_det]; norm_num
