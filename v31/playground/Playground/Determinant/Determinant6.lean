import Mathlib

namespace Determinant6

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-!
# Determinant of an 8×8 matrix over ZMod 13 via LU factorization

We define an 8×8 matrix `A₁₃` over `ZMod 13` and prove its determinant
is `9` by factoring it as `L₁₃ * U₁₃` where `L₁₃` is unit lower triangular
(det = 1) and `U₁₃` is upper triangular (det = product of diagonal).

Since `ZMod 13` is a field, the LU decomposition is exact with no scaling.
-/

def A₁₃ : Matrix (Fin 8) (Fin 8) (ZMod 13) :=
  !![ 1, 4, 6, 6, 6, 0, 2, 0;
      3, 6, 3, 3, 5, 3, 6, 1;
      0, 3, 0, 6, 3, 3, 4, 6;
      6, 0, 5, 3, 2, 5, 6, 1;
      4, 0, 2, 0, 0, 0, 5, 4;
      0, 3, 5, 1, 3, 5, 0, 4;
      1, 6, 3, 3, 4, 1, 2, 1;
      5, 1, 6, 3, 2, 0, 3, 6]

def L₁₃ : Matrix (Fin 8) (Fin 8) (ZMod 13) :=
  !![ 1,  0, 0,  0,  0,  0, 0, 0;
      3,  1, 0,  0,  0,  0, 0, 0;
      0,  6, 1,  0,  0,  0, 0, 0;
      6,  4, 10, 1,  0,  0, 0, 0;
      4,  7, 8,  5,  1,  0, 0, 0;
      0,  6, 9, 11,  9,  1, 0, 0;
      1,  4, 8, 10, 10,  5, 1, 0;
      5,  1, 9,  7, 10,  0, 3, 1]

def U₁₃ : Matrix (Fin 8) (Fin 8) (ZMod 13) :=
  !![ 1, 4,  6,  6, 6,  0, 2,  0;
      0, 7, 11, 11, 0,  3, 0,  1;
      0, 0, 12,  5, 3, 11, 4,  0;
      0, 0,  0,  3, 1,  0, 6, 10;
      0, 0,  0,  0, 12, 8, 0, 12;
      0, 0,  0,  0, 0, 11, 2,  1;
      0, 0,  0,  0, 0,  0, 2,  6;
      0, 0,  0,  0, 0,  0, 0,  5]

lemma A₁₃_eq_LU : A₁₃ = L₁₃ * U₁₃ := by decide +kernel

lemma L₁₃_det : L₁₃.det = 1 := by
  simp only [L₁₃]
  rw [Matrix.det_of_lowerTriangular]
  · decide
  · unfold Matrix.BlockTriangular; decide

lemma U₁₃_det : U₁₃.det = 9 := by
  simp only [U₁₃]
  rw [Matrix.det_of_upperTriangular]
  · decide
  · unfold Matrix.BlockTriangular; decide

theorem A₁₃_det : A₁₃.det = 9 := by
  rw [A₁₃_eq_LU, Matrix.det_mul, L₁₃_det, U₁₃_det]
  decide

end Determinant6
