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

lemma det_of_smul_det {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ} {d : ℤ}
    (hk : k ≠ 0)
    (h : (k • M).det = k ^ n * d) :
    M.det = d := by
  rw [Matrix.det_smul, Fintype.card_fin] at h
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

lemma E₈_L_det : E₈_L.det = 116640000000 := by
  simp only [E₈_L]
  rw [Matrix.det_of_lowerTriangular]
  · decide
  · unfold Matrix.BlockTriangular; decide

lemma E₈_U_det : E₈_U.det = 1440 := by
  simp only [E₈_U]
  rw [Matrix.det_of_upperTriangular]
  · decide
  · unfold Matrix.BlockTriangular; decide

theorem E₈_det' : E₈.det = 1 := by
  apply det_of_smul_det (k := 60) (by norm_num)
  erw [show 60 • E₈ = E₈_L * E₈_U by decide]
  grind [E₈_L_det, E₈_U_det, Matrix.det_mul]

universe v
variable {α β m n o : Type*} {m' n' : α → Type*}
variable {R : Type v} {M N : Matrix m m R} {b : m → α}

abbrev IsUpperTriangular [LT m] [Zero R] (M : Matrix m m R) : Prop := M.BlockTriangular id

example : IsUpperTriangular E₈_U := by
  unfold IsUpperTriangular
  unfold Matrix.BlockTriangular
  decide
