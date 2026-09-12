import Playground.Lagarias.HarmonicBounds

/-!
# Elementary bounds for the Lagarias criterion

This module is independent of the still-incomplete RH equivalence in
`v32/Lagarias.lean`. No form of Robin's theorem is assumed here.

The imported lower comparison is Lagarias, arXiv:math/0008177, Lemma 3.1.
The upper estimate below is a variant of Lemma 3.2, valid for `n ≥ 27`
rather than `n ≥ 20`. That threshold suffices for the asymptotic argument.
-/

namespace LeanEval.NumberTheory.Lagarias

/-- An alias for the right-hand side of the elementary inequality. -/
noncomputable def rhs (n : ℕ) : ℝ := bound n

lemma log_add_one_le_log_add_inv {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) ≤ Real.log x + 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hx)] at h
  have hdiv : (x + 1) / x - 1 = 1 / x := by
    rw [add_div, div_self (ne_of_gt hx)]
    ring
  rw [hdiv] at h
  linarith

/-- An explicit one-sided error estimate, obtained without Euler--Maclaurin. -/
lemma harmonic_lt_log_add_gamma_add_inv {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) <
      Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  linarith [harmonic_lt_log_add_one_add_gamma n, log_add_one_le_log_add_inv hnR]

lemma harmonic_pos {n : ℕ} (hn : 0 < n) : 0 < (harmonic n : ℝ) :=
  zero_lt_one.trans_le (one_le_harmonic_real hn)

lemma harmonic_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := harmonic_nonneg_real n

lemma one_lt_log {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log (n : ℝ) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (Real.lt_log_iff_exp_lt (by linarith : 0 < (n : ℝ))).2
  exact Real.exp_one_lt_three.trans_le hnR

lemma robinBound_lt_rhs {n : ℕ} (hn : 3 ≤ n) : robinBound n < rhs n := by
  have h := robinBound_le_exp_harmonic_mul_log_harmonic hn
  have hpos := harmonic_pos (show 0 < n by omega)
  dsimp [rhs, bound]
  linarith

@[simp] lemma rhs_one : rhs 1 = 1 := by
  norm_num [rhs, bound, harmonic_succ]

lemma exp_gamma_lt_three : Real.exp Real.eulerMascheroniConstant < 3 := by
  have hgamma : Real.eulerMascheroniConstant < 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  exact (Real.exp_lt_exp.mpr hgamma).trans Real.exp_one_lt_three

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

/-- The first four terms of the exponential series control the smaller error terms. -/
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

lemma log_harmonic_le_log_log_add_inv {n : ℕ} (hn : 3 ≤ n) :
    Real.log (harmonic n : ℝ) ≤
      Real.log (Real.log (n : ℝ)) + 1 / Real.log (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have ht0 : 0 < Real.log (n : ℝ) := by linarith [one_lt_log hn]
  calc
    Real.log (harmonic n : ℝ) ≤ Real.log (Real.log (n : ℝ) + 1) := by
      apply Real.log_le_log (harmonic_pos hnpos)
      linarith [harmonic_le_one_add_log n]
    _ ≤ _ := log_add_one_le_log_add_inv ht0

/-- A fully explicit eventual version of Lagarias, Lemma 3.2. -/
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
    _ ≤ robinBound n + 7 * x / t := by nlinarith
    _ = robinBound n + 7 * (n : ℝ) / Real.log (n : ℝ) := rfl

end LeanEval.NumberTheory.Lagarias
