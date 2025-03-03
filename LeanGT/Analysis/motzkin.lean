import Mathlib
import LeanGT.Texify

set_option linter.unusedTactic false

example : True := by
  texify
  exact trivial

theorem motzkin (x y : ℝ) : 0 ≤ x^4 * y^2 + x^2 * y^4  - 3 * x^2 * y^2 + 1 := by
  texify

  let w : Fin 3 → ℝ := fun _ => (1:ℝ)/3

  let f : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => x^4 * y^2
    | 1 => x^2 * y^4
    | 2 => 1

  have amgm := Real.geom_mean_le_arith_mean_weighted {0, 1, 2} w f (by
    intro _ _
    positivity
  ) (by
    simp
    norm_num
  ) (by
    intro i _
    fin_cases i <;> positivity
  )

  simp at amgm
  unfold w at amgm
  unfold f at amgm
  dsimp at amgm

  norm_num at amgm

  rw [←Real.mul_rpow (by positivity) (by positivity)] at amgm
  rw [show x ^ 4 * y ^ 2 * (x ^ 2 * y ^ 4) = (x * y) ^ 6 by ring] at amgm
  rw [show ((x * y) ^ 6) ^ ((1:ℝ) / 3) = (x * y)^2 by
    rw [show (x * y) ^ 6 = ((x * y) ^ 2)^3 by ring]
    rw [show ((x * y) ^ 2)^3 = ((x * y) ^ 2)^(3:ℝ) by norm_cast]
    rw [←Real.rpow_mul (by positivity)]
    norm_num
  ] at amgm

  linarith
