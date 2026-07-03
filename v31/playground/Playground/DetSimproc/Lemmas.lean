import Mathlib

/-!
# Foundation lemmas for the determinant simproc

These lemmas justify the row operations used by Gaussian elimination
to compute integer matrix determinants.
-/

namespace DetSimproc

/-- Row combination: replace row `i` with `a • row i + b • row j`.
    The determinant scales by `a`. -/
lemma det_rowCombine {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ}
    (i j : Fin n) (a b : ℤ)
    (h : (M.updateRow i (a • M i + b • M j)).det = a * k)
    (hij : i ≠ j) (ha : a ≠ 0) :
    M.det = k := by
  have h1 := M.det_updateRow_add i (a • M i) (b • M j)
  have h2 := M.det_updateRow_smul i a (M i)
  have h3 := M.updateRow_eq_self i
  have h4 := M.det_updateRow_smul i b (M j)
  have h5 := M.det_updateRow_eq_zero hij.symm
  rw [h2, h3, h4, h5, mul_zero, add_zero] at h1
  rw [h1] at h
  exact mul_left_cancel₀ ha h

/-- Row swap: swapping rows `i` and `j` negates the determinant. -/
lemma det_rowSwap {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ}
    (i j : Fin n)
    (h : (M.submatrix (Equiv.swap i j) id).det = -k)
    (hij : i ≠ j) :
    M.det = k := by
  have h1 := M.det_permute (Equiv.swap i j)
  simp [Equiv.Perm.sign_swap hij, Units.val_neg, Units.val_one] at h1
  -- h1 : M.det = -(M.submatrix ...).det
  linarith

/-- Upper-triangular finish: determinant equals product of diagonal entries. -/
lemma det_upperTriangular_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ}
    (h_tri : M.BlockTriangular id)
    (h_prod : ∏ i : Fin n, M.diag i = k) :
    M.det = k := by
  rw [Matrix.det_of_upperTriangular h_tri]
  exact h_prod

end DetSimproc
