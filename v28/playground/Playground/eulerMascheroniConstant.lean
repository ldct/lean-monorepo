import Mathlib

lemma hγ_lo : (0.577215 : ℝ) ≤ Real.eulerMascheroniConstant := sorry
lemma hγ_hi : Real.eulerMascheroniConstant ≤ 0.577216 := sorry

-- log(log 2) bounds (sorry'd)
lemma hll_lo : (-0.366513 : ℝ) ≤ Real.log (Real.log 2) := sorry
lemma hll_hi : Real.log (Real.log 2) ≤ -0.366512 := sorry

-- Series sum bounds (sorry'd)
lemma hs_lo : (0.834438 : ℝ) ≤
  ∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := sorry
lemma hs_hi :
  ∑' n : ℕ, (Real.log 2) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) ≤
    0.834440 := sorry
