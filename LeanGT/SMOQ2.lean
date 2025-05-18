import Mathlib
import LeanTeXMathlib
import Plausible

open Real

theorem t1 : (sqrt 10 + sqrt 2)^2 = 12 + 4 * sqrt 5 := by
  calc
    (sqrt 10 + sqrt 2) ^ 2 = (sqrt 10) ^ 2 + (sqrt 2) ^ 2 + 2 * (sqrt 10 * sqrt 2) := by ring
    _ = 12 + 2 * (sqrt 10 * sqrt 2) := by
      have h1 : (sqrt 10) ^ 2 = 10 := sq_sqrt (by positivity)
      have h2 : (sqrt 2) ^ 2 = 2 := sq_sqrt (by positivity)
      rw [h1, h2]
      ring
    _ = 12 + 4 * sqrt 5 := by
      have h4 : sqrt 10 * sqrt 2 = 2 * sqrt 5 := by
        calc
          sqrt 10 * sqrt 2 = sqrt (10 * 2) := by rw [sqrt_mul (by positivity)]
          _ = sqrt (2^2 * 5) := by norm_num
          _ = (sqrt (2^2)) * sqrt 5 := by rw [sqrt_mul (by positivity)]
          _ = (2 : ℝ) * sqrt 5 := by rw [sqrt_sq (by positivity)]
          _ = 2 * sqrt 5 := by ring
      rw [h4]
      ring

theorem t2 : (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) = 24 + 8 * sqrt 5 := by
  have h1 : (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) =
      ((sqrt 10 - sqrt 2) * (sqrt 10 + sqrt 2))^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(2 : ℝ) := by
    have h2 : (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) =
        (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(2 : ℝ) := by
      have h3 : (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) = (sqrt 10 + sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(2 : ℝ) := by
        have h4 : (sqrt 10 + sqrt 2)^(7 / 3 : ℝ) = (sqrt 10 + sqrt 2)^(1 / 3 + 2 : ℝ) := by norm_num
        rw [h4]
        rw [rpow_add]
        positivity
      rw [h3]
      ring_nf
    rw [h2]
    have h5 : (sqrt 10 - sqrt 2)^(1 / 3 : ℝ) * (sqrt 10 + sqrt 2)^(1 / 3 : ℝ) = ((sqrt 10 - sqrt 2) * (sqrt 10 + sqrt 2))^(1 / 3 : ℝ) := by
      rw [← mul_rpow]
      norm_num
      positivity
    rw [h5]
  rw [h1]
  have h2 := by
    calc
      (sqrt 10 - sqrt 2) * (sqrt 10 + sqrt 2)
        = ((sqrt 10) ^ 2 - (sqrt 2) ^ 2 : ℝ) := by ring
      _ = 8 := by simp [sq_sqrt] ; norm_num
  have h3 : ((sqrt 10 - sqrt 2) * (sqrt 10 + sqrt 2) : ℝ)^(1 / 3 : ℝ) = (2 : ℝ) := by
    rw [h2]
    have h4 : 8 ^ (1 / 3 : ℝ) = (2 : ℝ) := by
      have h5 : 8 ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by norm_num
      rw [h5]
      rw [← rpow_mul]
      norm_num
      norm_num
    rw [h4]
  rw [h3]
  have h5 : (sqrt 10 + sqrt 2) ^ (2 : ℝ) = (12 + 4 * sqrt 5 : ℝ) := by
    have h6 : (sqrt 10 + sqrt 2) ^ (2 : ℝ) = (sqrt 10 + sqrt 2) ^ 2 := by
      norm_cast
    rw [h6]
    have h7 : (sqrt 10 + sqrt 2) ^ 2 = (sqrt 10) ^ 2 + (sqrt 2) ^ 2 + 2 * (sqrt 10 * sqrt 2) := by
      ring
    rw [h7]
    have h8 : (sqrt 10) ^ 2 = (10 : ℝ) := sq_sqrt (by norm_num)
    have h9 : (sqrt 2) ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
    have h10 : sqrt 10 * sqrt 2 = sqrt 20 := by
      rw [← sqrt_mul (by norm_num)]
      norm_num
    have h11 : sqrt 20 = 2 * sqrt 5 := by
      rw [sqrt_eq_iff_mul_self_eq] <;> norm_num
      ring_nf
      norm_num
    rw [h8, h9, h10, h11]
    ring
  rw [h5]
  ring
