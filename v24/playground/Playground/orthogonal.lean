import Mathlib

theorem norm_orthogonal (n : ℕ)
  (A : Matrix.orthogonalGroup (Fin n) ℝ)
  (v : EuclideanSpace ℝ (Fin n))
: ‖A • v‖ = ‖v‖ := by
  have := A.2.2
  rw [ EuclideanSpace.norm_eq, EuclideanSpace.norm_eq ]

  have h_norm_sq : (A.val.mulVec v) ⬝ᵥ (A.val.mulVec v) = v ⬝ᵥ v := by
    simp_all [ Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
    erw [ A.2.1 ]
    norm_num

  have h_norm_sq : ∑ i, (A.val.mulVec v i) ^ 2 = ∑ i, (v i) ^ 2 := by
    simp only [ sq  ]
    exact h_norm_sq

  simp_all [ Matrix.mulVec, dotProduct ]
  exact congrArg Real.sqrt h_norm_sq
