import Playground.Determinant2

def A₂₀ : Matrix (Fin 20) (Fin 20) ℤ :=
  !![    2,   -3,    2,    3,    0,   -2,    1,   -3,   -1,    0,    1,   -2,   -3,    0,    0,   -3,   -3,   -3,    3,   -2;
         4,   -7,    1,    6,   -3,   -3,   -1,   -5,   -1,   -3,    5,   -6,   -3,   -2,   -3,   -4,   -8,   -3,    9,   -2;
         0,   -2,   -7,    0,   -7,    3,   -9,    3,   -1,   -5,    4,   -6,    3,   -6,   -5,    1,   -7,    9,    4,    5;
         0,    0,   -2,    1,   -5,    3,   -6,    5,   -7,    2,   -1,   -3,   -8,   -1,    4,   -7,   -5,    6,   -3,    5;
         0,    0,    0,    1,   -4,    1,    2,    0,    2,    2,    4,    1,    0,    4,   -1,    2,    0,    3,    2,    6;
         0,    0,    0,    0,   -1,    1,    1,   -5,    4,    3,    2,   -1,    0,    4,   -4,    2,   -2,    2,   -2,    4;
         0,    0,    0,    0,    0,   -2,    3,    6,    1,   -3,   -1,    1,    5,   -4,    0,   -1,    1,    4,    7,   -1;
         0,    0,    0,    0,    0,    0,   -1,    0,   -2,    2,    0,   -1,    0,   -2,    5,    2,    2,   -4,   -2,    0;
         0,    0,    0,    0,    0,    0,    0,   -2,   -2,    0,    0,    2,    1,   -3,   -5,   -1,   -3,    0,   -1,    1;
         0,    0,    0,    0,    0,    0,    0,    0,   -1,    0,    4,    1,    5,   -5,   -3,   -1,   -5,   -5,   -1,    2;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    2,   -5,   -4,   -8,    7,    4,   -4,    8,    5,   -3,    2;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    1,   -1,    0,    5,    1,    0,    1,   -3,   -1,    0;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,   -1,    0,    1,    1,    1,   -1,   -1,    1,    0;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,   -2,   -2,    2,   -3,    1,    6,    1,    5;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    2,    2,    2,   -1,    7,    2,    3;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    2,   -1,    1,    1,    3,    2;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,   -2,   -3,   -3,   -2,    1;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,   -2,   -1,   -3,    0;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,   -1,    4,    4;
         0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,    1,    4]

set_option maxHeartbeats 800000 in -- 20×20 matrix row reduction (19 steps)
set_option linter.flexible false in
theorem A₂₀_det : A₂₀.det = 32 := by
  apply my_helper 1 0 (2:ℤ) (-4:ℤ)
  simp [A₂₀, updateRowSimproc, mySimproc]
  apply my_helper 2 1 (-2:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 3 2 (2:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 4 3 (2:ℤ) (-1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 5 4 (-2:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 6 5 (-2:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 7 6 (-2:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 8 7 (-4:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 9 8 (4:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 10 9 (-4:ℤ) (-2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 11 10 (-4:ℤ) (-1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 12 11 (-4:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 13 12 (-8:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 14 13 (-8:ℤ) (-2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 15 14 (16:ℤ) (-2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 16 15 (16:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 17 16 (16:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 18 17 (16:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 19 18 (16:ℤ) (-1:ℤ)
  simp [updateRowSimproc, mySimproc]
  rw [Matrix.det_of_upperTriangular]
  · decide +kernel
  · unfold Matrix.BlockTriangular; decide +kernel
