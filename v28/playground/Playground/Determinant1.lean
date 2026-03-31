import Mathlib

def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

variable {n : Type*} [Fintype n] [DecidableEq n] in
lemma my_helper {M : Matrix n n ℤ} {k : ℤ} (i j : n) (a b : ℤ)
    (h : (M.updateRow i (a • M i + b • M j)).det = a * k)
    (hij : i ≠ j := by decide) (ha : a ≠ 0 := by decide) :
    M.det = k := by
  simpa only [M.det_updateRow_add, M.det_updateRow_smul, M.det_updateRow_eq_zero hij.symm,
    M.updateRow_eq_self, add_zero, mul_zero, mul_eq_mul_left_iff, ha, or_false] using h

theorem E₈_det : E₈.det = 1 := by
  apply my_helper 2 0 (2:ℤ) (1:ℤ)
  apply my_helper 3 1 (2:ℤ) (1:ℤ)
  apply my_helper 3 2 (3:ℤ) (2:ℤ)
  apply my_helper 4 3 (5:ℤ) (1:ℤ)
  apply my_helper 5 4 (4:ℤ) (1:ℤ)
  apply my_helper 6 5 (3:ℤ) (1:ℤ)
  apply my_helper 7 6 (2:ℤ) (1:ℤ)
  rw [Matrix.det_of_upperTriangular]
  · decide +kernel
  · unfold Matrix.BlockTriangular; decide +kernel
