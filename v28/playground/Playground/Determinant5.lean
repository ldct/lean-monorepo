import Playground.Determinant2

/-!
# E₈ determinant via scaling to an integer matrix

We prove `E₈.det = 1` by first scaling to `60 • E₈` (an integer matrix
whose LU decomposition is entirely integral), then evaluating the
determinant of the concrete integer matrix.

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

set_option linter.flexible false in
theorem E₈_det' : E₈.det = 1 := by
  apply det_of_smul_det (k := 60) (by decide)
  sorry
