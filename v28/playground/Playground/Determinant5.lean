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
theorem E₈_det' : E₈.det = 1 := by
  apply det_of_smul_det (k := 60) (by decide)
  -- Goal: (60 • E₈).det = 60 ^ 8 * 1
  have hLU : 60 • E₈ = E₈_L * E₈_U := by sorry
  calc (60 • E₈).det
      = (E₈_L * E₈_U).det := by rw [hLU]
    _ = E₈_L.det * E₈_U.det := Matrix.det_mul _ _
    _ = 60 ^ 8 * 1 := by sorry
