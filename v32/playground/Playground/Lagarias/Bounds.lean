import Playground.Lagarias.Basic

/-!
# An eventual upper bound for Lagarias' criterion

This variant of Lagarias, arXiv:math/0008177, Lemma 3.2 proves the error
bound with constant 7 for `n ≥ 27`. The later threshold is sufficient
for the asymptotic argument. No form of Robin's theorem is assumed.
-/

namespace LeanEval.NumberTheory.Lagarias

lemma three_lt_log {n : ℕ} (hn : 27 ≤ n) : 3 < Real.log (n : ℝ) := by
  have hnR : (27 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : Real.exp (3 : ℝ) < 27 := by
    calc
      Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      _ < (3 : ℝ) * 3 * 3 := by
        gcongr <;> exact Real.exp_one_lt_three
      _ = 27 := by norm_num
  exact (Real.lt_log_iff_exp_lt (by linarith : 0 < (n : ℝ))).2 (he.trans_le hnR)

/-- Four terms of the exponential series control the smaller errors. -/
lemma log_add_one_le_div_log {n : ℕ} (hn : 27 ≤ n) :
    Real.log (n : ℝ) + 1 ≤ (n : ℝ) / Real.log (n : ℝ) := by
  let t := Real.log (n : ℝ)
  have ht3 : 3 < t := three_lt_log hn
  have ht0 : 0 < t := by linarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hseries := Real.sum_le_exp_of_nonneg ht0.le 4
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at hseries
  have heq : Real.exp t = (n : ℝ) := Real.exp_log hnR
  simp only [heq] at hseries
  apply (le_div_iff₀ ht0).2
  have hcube : 0 ≤ (t - 3) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg t)
  nlinarith

/-- An explicit eventual version of Lagarias, Lemma 3.2. -/
theorem rhs_le_robinBound_add_error {n : ℕ} (hn : 27 ≤ n) :
    rhs n ≤ robinBound n + 7 * (n : ℝ) / Real.log (n : ℝ) := by
  let x : ℝ := n
  let t := Real.log (n : ℝ)
  let e := Real.exp Real.eulerMascheroniConstant
  let u := Real.log t
  have hnpos : 0 < n := by omega
  have hx0 : 0 < x := by dsimp [x]; exact_mod_cast hnpos
  have ht3 : 3 < t := three_lt_log hn
  have ht0 : 0 < t := by linarith
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith : 1 ≤ t)
  have he0 : 0 < e := Real.exp_pos _
  have he3 : e ≤ 3 := exp_gamma_lt_three.le
  have hH : (harmonic n : ℝ) ≤ t + 1 := by
    simpa [t, add_comm] using harmonic_le_one_add_log n
  have hE : Real.exp (harmonic n : ℝ) ≤ e * (x + 1) :=
    (exp_harmonic_lt_exp_gamma_mul_add_one n).le
  have hlogH : Real.log (harmonic n : ℝ) ≤ u + 1 / t :=
    log_harmonic_le_log_log_add_inv (by omega : 3 ≤ n)
  have hlogH0 : 0 ≤ Real.log (harmonic n : ℝ) :=
    Real.log_nonneg (one_le_harmonic_real hnpos)
  have hmul : Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) ≤
      (e * (x + 1)) * (u + 1 / t) :=
    mul_le_mul hE hlogH hlogH0 (by positivity)
  have hbudget : t + 1 ≤ x / t := log_add_one_le_div_log hn
  have huUpper : u ≤ t := by
    have h := Real.log_le_sub_one_of_pos ht0
    dsimp [u]
    linarith
  have hinv : 1 / t ≤ 1 := (div_le_iff₀ ht0).2 (by linarith)
  have hextra : e * (u + 1 / t) ≤ 3 * (t + 1) :=
    mul_le_mul he3 (by linarith) (by positivity) (by norm_num)
  have hextra' : e * (u + 1 / t) ≤ 3 * (x / t) :=
    hextra.trans (by linarith)
  have hterm : e * x / t ≤ 3 * (x / t) := by
    simpa [mul_div_assoc] using
      mul_le_mul_of_nonneg_right he3 (by positivity : 0 ≤ x / t)
  calc
    rhs n = (harmonic n : ℝ) +
        Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := rfl
    _ ≤ (t + 1) + (e * (x + 1)) * (u + 1 / t) := add_le_add hH hmul
    _ = robinBound n + (t + 1) + e * x / t + e * (u + 1 / t) := by
      dsimp [robinBound, x, t, e, u]
      ring
    _ ≤ robinBound n + (x / t) + 3 * (x / t) + 3 * (x / t) := by
      linarith only [hbudget, hterm, hextra']
    _ = robinBound n + 7 * x / t := by ring
    _ = robinBound n + 7 * (n : ℝ) / Real.log (n : ℝ) := rfl

end LeanEval.NumberTheory.Lagarias
