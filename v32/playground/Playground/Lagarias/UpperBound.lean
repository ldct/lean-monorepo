import Playground.Lagarias.Bounds

/-!
# An upper error bound for the Lagarias right-hand side

This gives the estimate needed from Lemma 3.2 of Lagarias with the less sharp
constant 22 and the simpler range `n >= 3`. The reverse implication needs a fixed
constant, not specifically the constant 7 in the paper.

The proof uses the already formalized shifted harmonic bounds. In particular,
`exp(H_n) < exp(gamma) * (n + 1)` avoids estimating an exponential remainder.
-/

namespace LeanEval.NumberTheory.Lagarias

lemma exp_gamma_lt_three : Real.exp Real.eulerMascheroniConstant < 3 := by
  apply lt_trans (Real.exp_lt_exp.mpr (show Real.eulerMascheroniConstant < 1 by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]))
  exact Real.exp_one_lt_three

lemma exp_harmonic_lt_exp_gamma_mul_add_one (n : ℕ) :
    Real.exp (harmonic n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * ((n : ℝ) + 1) := by
  have h := Real.exp_lt_exp.mpr (harmonic_lt_log_add_one_add_gamma n)
  rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h
  simpa [mul_comm] using h

lemma harmonic_le_log_add_two {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) ≤ Real.log (n : ℝ) + 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hinv : (1 : ℝ) / (n : ℝ) ≤ 1 :=
    (div_le_iff₀ hnR).2 (by simpa using hn1)
  linarith [harmonic_lt_log_add_gamma_add_inv hn,
    Real.eulerMascheroniConstant_lt_two_thirds]

lemma log_harmonic_le_log_log_add_div {n : ℕ} (hn : 3 ≤ n) :
    Real.log (harmonic n : ℝ) ≤
      Real.log (Real.log (n : ℝ)) + 2 / Real.log (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have ht : 0 < Real.log (n : ℝ) := by linarith [one_lt_log hn]
  have hH := Real.log_le_log (harmonic_pos hnpos) (harmonic_le_log_add_two hnpos)
  have h := Real.log_le_sub_one_of_pos
    (show 0 < (Real.log (n : ℝ) + 2) / Real.log (n : ℝ) by positivity)
  rw [Real.log_div (by positivity) ht.ne'] at h
  have hdiv : (Real.log (n : ℝ) + 2) / Real.log (n : ℝ) - 1 =
      2 / Real.log (n : ℝ) := by
    rw [add_div, div_self ht.ne']
    ring
  rw [hdiv] at h
  linarith

/-- A convenient coarse bound from the first three terms of the exponential series. -/
lemma log_sq_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 2 * x := by
  have hxpos : 0 < x := by linarith
  have ht := Real.log_nonneg hx
  have h := Real.sum_le_exp_of_nonneg ht 3
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  rw [Real.exp_log hxpos] at h
  nlinarith

/-- The quantitative upper comparison needed in the reverse Lagarias implication. -/
theorem rhs_le_robinBound_add_error {n : ℕ} (hn : 3 ≤ n) :
    rhs n ≤ robinBound n + 22 * (n : ℝ) / Real.log (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have ht1 := one_lt_log hn
  have ht : 0 < Real.log (n : ℝ) := by linarith
  have htN : Real.log (n : ℝ) ≤ (n : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hnR]
  have ht2 := log_sq_le_two_mul hn1
  have hu : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg ht1.le
  have ha := Real.exp_pos Real.eulerMascheroniConstant
  have ha3 := exp_gamma_lt_three
  have hLH : 0 ≤ Real.log (harmonic n : ℝ) := by
    apply Real.log_nonneg
    linarith [log_add_gamma_lt_harmonic hnpos, gamma_pos]
  have hlog := mul_le_mul_of_nonneg_right (log_harmonic_le_log_log_add_div hn) ht.le
  rw [add_mul, div_mul_cancel₀ _ ht.ne'] at hlog
  have hp := mul_le_mul (exp_harmonic_lt_exp_gamma_mul_add_one n).le hlog
    (mul_nonneg hLH ht.le)
    (mul_nonneg ha.le (show 0 ≤ (n : ℝ) + 1 by positivity))
  have hHt : (harmonic n : ℝ) * Real.log (n : ℝ) ≤ 4 * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (harmonic_le_log_add_two hnpos) ht.le
    nlinarith
  have huT : Real.log (Real.log (n : ℝ)) * Real.log (n : ℝ) ≤
      (Real.log (n : ℝ)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos ht) ht.le
    nlinarith
  have haUT : Real.exp Real.eulerMascheroniConstant *
      Real.log (Real.log (n : ℝ)) * Real.log (n : ℝ) ≤ 6 * (n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left huT ha.le
    have h2 := mul_le_mul_of_nonneg_right ha3.le (sq_nonneg (Real.log (n : ℝ)))
    nlinarith
  have haN : 2 * Real.exp Real.eulerMascheroniConstant * ((n : ℝ) + 1) ≤
      12 * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right ha3.le
      (show 0 ≤ (n : ℝ) + 1 by positivity)
    nlinarith
  have hfinal : rhs n * Real.log (n : ℝ) ≤
      robinBound n * Real.log (n : ℝ) + 22 * (n : ℝ) := by
    dsimp [rhs, robinBound]
    nlinarith [hp]
  have herror : rhs n - robinBound n ≤ 22 * (n : ℝ) / Real.log (n : ℝ) :=
    (le_div_iff₀ ht).2 (by nlinarith [hfinal])
  linarith

end LeanEval.NumberTheory.Lagarias
