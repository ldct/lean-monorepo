/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aeb40357-796f-495a-8330-b9d5af48de07

The following was proved by Aristotle:

- lemma det_map_ℚ (M : Matrix (Fin 6) (Fin 6) ℤ): M.det = (M.map (Int.castRingHom ℚ)).det
-/

import Mathlib


def E₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2,  0, -1,  0,  0;
     -1,  0,  2, -1,  0,  0;
      0, -1, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -1;
      0,  0,  0,  0, -1,  2]

/-- E₆ viewed over ℚ. -/
def E₆Q : Matrix (Fin 6) (Fin 6) ℚ :=
  E₆.map (Int.castRingHom ℚ)

lemma det_map_ℚ (M : Matrix (Fin 6) (Fin 6) ℤ): M.det = (M.map (Int.castRingHom ℚ)).det := by
  -- Apply the fact that the determinant of a matrix over the integers is equal to the determinant of the same matrix when each entry is mapped to the rationals.
  apply Eq.symm; exact (by
  -- The determinant is a polynomial function of the entries of the matrix, and polynomials are compatible with ring homomorphisms. Therefore, the determinant of the matrix over the rationals is equal to the determinant of the matrix over the integers.
  have h_det_poly : ∀ (M : Matrix (Fin 6) (Fin 6) ℤ), Matrix.det (M.map (Int.castRingHom ℚ)) = Matrix.det M := by
    intro M
    exact (by
      have h_det_poly : ∀ (p : Polynomial ℤ), Polynomial.eval (1 : ℚ) (Polynomial.map (Int.castRingHom ℚ) p) = Polynomial.eval (1 : ℤ) p := by
        simp +decide [ Polynomial.eval_map ]
      -- The determinant is a polynomial function of the entries of the matrix, and polynomials are compatible with ring homomorphisms. Therefore, the determinant of the matrix over the rationals is equal to the determinant of the matrix over the integers. We can use the fact that the determinant is a polynomial function of the entries of the matrix.
      have h_det_poly : ∀ (M : Matrix (Fin 6) (Fin 6) ℤ), Matrix.det (M.map (Int.castRingHom ℚ)) = Polynomial.eval (1 : ℚ) (Polynomial.map (Int.castRingHom ℚ) (Matrix.det (Matrix.of (fun i j => Polynomial.X * Polynomial.C (M i j))))) := by
        -- The determinant is a polynomial function of the entries of the matrix, and polynomials are compatible with ring homomorphisms. Therefore, the determinant of the matrix over the rationals is equal to the determinant of the matrix over the integers. We can use the fact that the determinant is a polynomial function of the entries of the matrix and that polynomials are compatible with ring homomorphisms.
        have h_det_poly : ∀ (M : Matrix (Fin 6) (Fin 6) ℤ), Matrix.det (M.map (Int.castRingHom ℚ)) = Polynomial.eval (1 : ℚ) (Polynomial.map (Int.castRingHom ℚ) (Matrix.det (Matrix.of (fun i j => Polynomial.X * Polynomial.C (M i j))))) := by
          intro M
          have h_det_poly : Matrix.det (M.map (Int.castRingHom ℚ)) = Polynomial.eval (1 : ℚ) (Polynomial.map (Int.castRingHom ℚ) (Matrix.det (Matrix.of (fun i j => Polynomial.X * Polynomial.C (M i j))))) := by
            have h_det_poly : ∀ (i j : Fin 6), Polynomial.eval (1 : ℚ) (Polynomial.map (Int.castRingHom ℚ) (Polynomial.X * Polynomial.C (M i j))) = (M i j : ℚ) := by
              aesop
            -- The determinant of a matrix is a polynomial function of its entries. Therefore, if each entry of the matrix is a polynomial, then the determinant of the matrix is the determinant of the matrix with the polynomials evaluated at 1.
            have h_det_poly : ∀ (A : Matrix (Fin 6) (Fin 6) (Polynomial ℤ)), Polynomial.eval 1 (Polynomial.map (Int.castRingHom ℚ) (Matrix.det A)) = Matrix.det (Matrix.map A (fun p => Polynomial.eval 1 (Polynomial.map (Int.castRingHom ℚ) p))) := by
              simp +decide [ Matrix.det_apply' ];
              simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_prod ];
            rw [ h_det_poly ];
            exact congr_arg Matrix.det ( by ext i j; aesop )
          exact h_det_poly;
        assumption;
      convert h_det_poly M using 1;
      rw [ ‹∀ p : Polynomial ℤ, Polynomial.eval 1 ( Polynomial.map ( Int.castRingHom ℚ ) p ) = ( ↑ ( Polynomial.eval 1 p ) : ℚ ) › ] ; norm_num [ Matrix.det_apply' ] ; ring;
      norm_num [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_X, Polynomial.eval_C ]);
  -- Apply the hypothesis h_det_poly to the matrix M.
  apply h_det_poly)

/-- The unit-lower-triangular L factor (over ℚ). -/
def L₆ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ (1:ℚ), 0, 0, 0, 0, 0;
      0, (1:ℚ), 0, 0, 0, 0;
      (-(1:ℚ)/2), 0, (1:ℚ), 0, 0, 0;
      0, (-(1:ℚ)/2), (-(2:ℚ)/3), (1:ℚ), 0, 0;
      0, 0, 0, (-(6:ℚ)/5), (1:ℚ), 0;
      0, 0, 0, 0, (-(5:ℚ)/4), (1:ℚ) ]

/-- The upper-triangular U factor (over ℚ). -/
def U₆ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ (2:ℚ), 0, (-1:ℚ), 0, 0, 0;
      0, (2:ℚ), 0, (-1:ℚ), 0, 0;
      0, 0, (3:ℚ)/2, (-1:ℚ), 0, 0;
      0, 0, 0, (5:ℚ)/6, (-1:ℚ), 0;
      0, 0, 0, 0, (4:ℚ)/5, (-1:ℚ);
      0, 0, 0, 0, 0, (3:ℚ)/4 ]

theorem E₆_lu : E₆Q = L₆ * U₆ := by
  norm_num [E₆Q, E₆, L₆, U₆, Matrix.mul_apply]
  decide

lemma U₆_upperTriangular : U₆.BlockTriangular id := by
  simp +decide [Matrix.BlockTriangular]

lemma L₆_lowerTriangular : L₆.BlockTriangular OrderDual.toDual := by
  simp +decide [Matrix.BlockTriangular]

theorem L₆_det : L₆.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L₆ L₆_lowerTriangular]
  norm_num [Fin.prod_univ_succ, L₆]

theorem U₆_det : U₆.det = 3 := by
  rw [Matrix.det_of_upperTriangular U₆_upperTriangular]
  norm_num [Fin.prod_univ_succ, U₆]

theorem E₆Q_det : E₆Q.det = 3 := by
  rw [E₆Q_det]
  decide +kernel

theorem E₆_det : E₆.det = 3 := by
  native_decide +revert

/-- The Cartan matrix of type E₇. See [bourbaki1968] plate VI, page 281. -/
def E₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0, -1,  2]

/-- The Cartan matrix of type E₈. See [bourbaki1968] plate VII, page 285. -/
def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]