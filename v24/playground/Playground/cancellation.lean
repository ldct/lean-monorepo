import Mathlib
import Playground.Analysis.Cancel


namespace cancellation
open Cancel

example (a b k : ℕ) (k_pos : k ≠ 0) (eq : k*a = k*b) : a = b := by
  exact (Nat.mul_right_inj k_pos).mp eq


example {a b c : ℝ} {cpos : 0 < c} (h1 : c*a ≤ c*b) : a ≤ b := by
  cancel c at h1

example {a b c : ℝ} {cpos : 3 < c} (h1 : c*a ≤ c*b) : a ≤ b := by
  cancel c at h1

example (a b : ℕ) (h1 : a < b) : (2^a < 2^b) := by
  gcongr
  norm_num

example (a b k : ℕ) (h1 : a < b) : (k*a ≤ k*b) := by
  gcongr

example (a b k : ℝ) (kpos : 0 ≤ k) (h1 : a < b) : (k*a ≤ k*b) := by
  gcongr

example (a b k : ℝ) (kpos : 0 ≤ k) (h1 : a < b) : ((1/k+1)*a ≤ (1/k+1)*b) := by
  gcongr


end cancellation