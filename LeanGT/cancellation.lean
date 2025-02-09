import Mathlib
import LeanGT.Analysis.Cancel

example (a b k : ℕ) (k_pos : k ≠ 0) (eq : k*a = k*b) : a = b := by
  exact (Nat.mul_right_inj k_pos).mp eq

example (a b k : ℝ) (k_pos : k ≠ 0) (eq : k*a = k*b) : a = b := by
  exact mul_left_cancel₀ k_pos eq


example {a b c : ℝ} {cpos : 0 < c} (h1 : c*a ≤ c*b) : a ≤ b := by
  cancel c at h1

example {a b c : ℝ} {cpos : 3 < c} (h1 : c*a ≤ c*b) : a ≤ b := by
  cancel c at h1

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
    calc t * t = t ^ 2 := by ring
      _ = 3 * t := by rw [h1]

  cancel t at h3

  linarith [h3]


example (a b : ℕ) (h1 : a < b) : (2^a < 2^b) := by
  gcongr
  norm_num

example (a b k : ℕ) (h1 : a < b) : (k*a ≤ k*b) := by
  gcongr

example (a b k : ℝ) (kpos : 0 ≤ k) (h1 : a < b) : (k*a ≤ k*b) := by
  gcongr

example (a b k : ℝ) (kpos : 0 ≤ k) (h1 : a < b) : ((1/k+1)*a ≤ (1/k+1)*b) := by
  gcongr _ * ?_
