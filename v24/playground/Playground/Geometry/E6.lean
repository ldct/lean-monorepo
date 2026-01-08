import Mathlib

def E₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2,  0, -1,  0,  0;
     -1,  0,  2, -1,  0,  0;
      0, -1, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -1;
      0,  0,  0,  0, -1,  2]

/-- E₆ viewed over ℚ. -/
abbrev E₆Q : Matrix (Fin 6) (Fin 6) ℚ :=
  E₆.map (Int.castRingHom ℚ)


lemma det_map_ℚ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
: (M.map (Int.castRingHom ℚ)).det = M.det := by
  symm
  exact Int.cast_det _

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
  rw [E₆_lu, Matrix.det_mul]
  rw [L₆_det, U₆_det]
  norm_num

lemma test (t : ℤ) : (t : ℚ) = 3 ↔ t = 3 := by
  norm_cast

theorem E₆_det : E₆.det = 3 := by
  have := E₆Q_det
  rw [E₆Q, det_map_ℚ] at this
  rwa [test] at this


/-- The Cartan matrix of type E₇. See [bourbaki1968] plate VI, page 281. -/
def E₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0, -1,  2]


/-- E₇ viewed over ℚ. -/
def E₇Q : Matrix (Fin 7) (Fin 7) ℚ :=
  E₇.map (Int.castRingHom ℚ)

/-- The unit-lower-triangular L factor for E₇ (over ℚ). -/
def L₇ : Matrix (Fin 7) (Fin 7) ℚ :=
  !![ (1:ℚ), 0, 0, 0, 0, 0, 0;
      0, (1:ℚ), 0, 0, 0, 0, 0;
      (-(1:ℚ)/2), 0, (1:ℚ), 0, 0, 0, 0;
      0, (-(1:ℚ)/2), (-(2:ℚ)/3), (1:ℚ), 0, 0, 0;
      0, 0, 0, (-(6:ℚ)/5), (1:ℚ), 0, 0;
      0, 0, 0, 0, (-(5:ℚ)/4), (1:ℚ), 0;
      0, 0, 0, 0, 0, (-(4:ℚ)/3), (1:ℚ) ]

/-- The upper-triangular U factor for E₇ (over ℚ). -/
def U₇ : Matrix (Fin 7) (Fin 7) ℚ :=
  !![ (2:ℚ), 0, (-1:ℚ), 0, 0, 0, 0;
      0, (2:ℚ), 0, (-1:ℚ), 0, 0, 0;
      0, 0, (3:ℚ)/2, (-1:ℚ), 0, 0, 0;
      0, 0, 0, (5:ℚ)/6, (-1:ℚ), 0, 0;
      0, 0, 0, 0, (4:ℚ)/5, (-1:ℚ), 0;
      0, 0, 0, 0, 0, (3:ℚ)/4, (-1:ℚ);
      0, 0, 0, 0, 0, 0, (2:ℚ)/3 ]

theorem E₇_lu : E₇Q = L₇ * U₇ := by
  norm_num [E₇Q, E₇, L₇, U₇, Matrix.mul_apply]
  decide

lemma U₇_upperTriangular : U₇.BlockTriangular id := by
  simp +decide [Matrix.BlockTriangular]

lemma L₇_lowerTriangular : L₇.BlockTriangular OrderDual.toDual := by
  simp +decide [Matrix.BlockTriangular]

theorem L₇_det : L₇.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L₇ L₇_lowerTriangular]
  norm_num [Fin.prod_univ_succ, L₇]

theorem U₇_det : U₇.det = 2 := by
  rw [Matrix.det_of_upperTriangular U₇_upperTriangular]
  -- product of diagonal entries: 2 * 2 * (3/2) * (5/6) * (4/5) * (3/4) * (2/3) = 2
  norm_num [Fin.prod_univ_succ, U₇]

theorem E₇Q_det : E₇Q.det = 2 := by
  rw [E₇_lu, Matrix.det_mul]
  rw [L₇_det, U₇_det]
  norm_num

lemma test₂ (t : ℤ) : (t : ℚ) = 2 ↔ t = 2 := by
  norm_cast

theorem E₇_det : E₇.det = 2 := by
  have h := E₇Q_det
  rw [E₇Q, det_map_ℚ] at h
  rwa [test₂] at h

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

/-- E₈ viewed over ℚ. -/
def E₈Q : Matrix (Fin 8) (Fin 8) ℚ :=
  E₈.map (Int.castRingHom ℚ)

/-- The unit-lower-triangular L factor for E₈ (over ℚ). -/
def L₈ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![ (1:ℚ), 0, 0, 0, 0, 0, 0, 0;
      0, (1:ℚ), 0, 0, 0, 0, 0, 0;
      (-(1:ℚ)/2), 0, (1:ℚ), 0, 0, 0, 0, 0;
      0, (-(1:ℚ)/2), (-(2:ℚ)/3), (1:ℚ), 0, 0, 0, 0;
      0, 0, 0, (-(6:ℚ)/5), (1:ℚ), 0, 0, 0;
      0, 0, 0, 0, (-(5:ℚ)/4), (1:ℚ), 0, 0;
      0, 0, 0, 0, 0, (-(4:ℚ)/3), (1:ℚ), 0;
      0, 0, 0, 0, 0, 0, (-(3:ℚ)/2), (1:ℚ) ]

/-- The upper-triangular U factor for E₈ (over ℚ). -/
def U₈ : Matrix (Fin 8) (Fin 8) ℚ :=
  !![ (2:ℚ), 0, (-1:ℚ), 0, 0, 0, 0, 0;
      0, (2:ℚ), 0, (-1:ℚ), 0, 0, 0, 0;
      0, 0, (3:ℚ)/2, (-1:ℚ), 0, 0, 0, 0;
      0, 0, 0, (5:ℚ)/6, (-1:ℚ), 0, 0, 0;
      0, 0, 0, 0, (4:ℚ)/5, (-1:ℚ), 0, 0;
      0, 0, 0, 0, 0, (3:ℚ)/4, (-1:ℚ), 0;
      0, 0, 0, 0, 0, 0, (2:ℚ)/3, (-1:ℚ);
      0, 0, 0, 0, 0, 0, 0, (1:ℚ)/2 ]

example {G} (g : G) : g = g := by exact rfl

def my_theorem :=
#check Matrix.det_mul L₈ U₈

theorem prod_helper : (L₈ * U₈).det = L₈.det * U₈.det := Matrix.det_mul L₈ U₈

theorem E₈_lu : E₈Q = L₈ * U₈ := by
  norm_num [E₈Q, E₈, L₈, U₈, Matrix.mul_apply]
  decide

lemma U₈_upperTriangular : U₈.BlockTriangular id := by
  simp +decide [Matrix.BlockTriangular]

lemma L₈_lowerTriangular : L₈.BlockTriangular OrderDual.toDual := by
  simp +decide [Matrix.BlockTriangular]

theorem L₈_det : L₈.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L₈ L₈_lowerTriangular]
  norm_num [Fin.prod_univ_succ, L₈]

theorem U₈_det : U₈.det = 1 := by
  rw [Matrix.det_of_upperTriangular U₈_upperTriangular]
  norm_num [Fin.prod_univ_succ, U₈]

theorem helper : (L₈ * U₈).det = 1 := by
  rw [prod_helper, L₈_det, U₈_det]
  norm_num

theorem E₈Q_det : E₈Q.det = 1 := by
  rw [E₈_lu]
  exact helper

lemma test₁ (t : ℤ) : (t : ℚ) = 1 ↔ t = 1 := by
  norm_cast

theorem E₈_det : E₈.det = 1 := by
  have h := E₈Q_det
  rw [E₈Q, det_map_ℚ] at h
  exact (test₁ (E₈.det)).1 h

#check Matrix (Fin n) (Fin n) ℚ
