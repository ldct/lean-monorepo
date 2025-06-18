import Mathlib
import LeanTeXMathlib

example (n : ℕ) (s : Finset ℕ)
: (∑ x ∈ s, 1) * n = (∑ x ∈ s, n) := by
  rw [Finset.sum_const]
  simp

example : Monotone (fun x: NNReal ↦ x ^ ((1:ℝ)/2)) := by
  apply NNReal.monotone_rpow_of_nonneg
  positivity

example (a b c : ℝ) (ha : 0 < a) : ((a^b)^c = a^(b*c)) := by
  exact Eq.symm (Real.rpow_mul (le_of_lt ha) b c)

example (a b c : ℝ) (ha : 0 < a) : (a^b * a^c = a^(b+c)) := by
  rw [Real.rpow_add ha]

example (a b : ℝ) (ha : 0 ≤ a) : (a^b)⁻¹ = (a^(-b)) := by
  rw [Real.rpow_neg ha]

theorem test (p : ℝ) (x : ℕ): (2:ℝ)^x * ((2:ℝ)^x)⁻¹^p = ((2:ℝ)^x)^(1-p) := by
  have : ((2:ℝ) ^ x)⁻¹ = (2 ^ (-(x:ℝ))) := by
    simp [Real.rpow_neg]
  rw [this]
  simp [←Real.rpow_mul]
  have : ((2:ℝ) ^ x) ^ (1 - p) = (2 ^ (x * (1 - p))) := by
    rw [Real.rpow_mul (by norm_num)]
    norm_cast
  rw [this]
  have : (2:ℝ) ^ x * 2 ^ (-((x : ℝ) * p)) = 2 ^ (x + -((x : ℝ) * p)) := by
    rw [Real.rpow_add (by norm_num)]
    norm_cast
  rw [this]
  congr
  ring

example (p : ℝ) (n : ℕ) : (n < n + 1) := by
  omega

example (n : ℕ) : (1 ≤ 2^n) := by
  exact Nat.one_le_two_pow

example (n : ℕ) : (1 ≤ 2^n) := by
  omega

example (x y : ℝ)
: abs (x^2 + y^2) = x^2 + y^2 := by

: 0 ≤ x^2 + y^2 := by positivity
