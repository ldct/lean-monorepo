import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Elementary harmonic comparisons for Lagarias' criterion

This module proves the lower comparison (Lagarias, arXiv:math/0008177,
Lemma 3.1) and the common estimates used by the upper comparisons.
It does not assume RH or any form of Robin's theorem.
-/

namespace LeanEval.NumberTheory.Lagarias

/-- The right-hand side of Lagarias' elementary inequality. -/
noncomputable def rhs (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- Alternative name retained for the exponential-logarithmic comparison API. -/
noncomputable abbrev bound (n : ℕ) : ℝ := rhs n

/-- The main term in Robin's divisor-sum estimate. -/
noncomputable def robinBound (n : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))

lemma gamma_pos : 0 < Real.eulerMascheroniConstant := by
  linarith [Real.one_half_lt_eulerMascheroniConstant]

lemma log_add_gamma_lt_harmonic {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) + Real.eulerMascheroniConstant < (harmonic n : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', Nat.ne_of_gt hn, if_false] at h
  linarith

lemma harmonic_lt_log_add_one_add_gamma (n : ℕ) :
    (harmonic n : ℝ) < Real.log ((n : ℝ) + 1) + Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  dsimp [Real.eulerMascheroniSeq] at h
  linarith

lemma log_add_one_le_log_add_inv {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) ≤ Real.log x + 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hx)] at h
  have hdiv : (x + 1) / x - 1 = 1 / x := by
    rw [add_div, div_self (ne_of_gt hx)]
    ring
  rw [hdiv] at h
  linarith

/-- A one-sided harmonic error bound, without Euler--Maclaurin. -/
lemma harmonic_lt_log_add_gamma_add_inv {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) <
      Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  linarith [harmonic_lt_log_add_one_add_gamma n, log_add_one_le_log_add_inv hnR]

lemma harmonic_pos {n : ℕ} (hn : 0 < n) : 0 < (harmonic n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  linarith [log_add_gamma_lt_harmonic hn, gamma_pos]

lemma harmonic_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (harmonic_pos hn).le

lemma harmonic_nonneg_real (n : ℕ) : 0 ≤ (harmonic n : ℝ) := harmonic_nonneg n

lemma harmonic_monotone_real : Monotone (fun n : ℕ ↦ (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  have h : harmonic n ≤ harmonic (n + 1) := by
    rw [harmonic_succ]
    have h0 : (0 : ℚ) ≤ (↑(n + 1))⁻¹ := by positivity
    linarith
  exact_mod_cast h

lemma one_le_harmonic_real {n : ℕ} (hn : 0 < n) : 1 ≤ (harmonic n : ℝ) := by
  have h := harmonic_monotone_real (show 1 ≤ n by omega)
  norm_num [harmonic_succ] at h
  exact h

lemma log_lt_harmonic {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) < (harmonic n : ℝ) := by
  linarith [log_add_gamma_lt_harmonic hn, gamma_pos]

lemma exp_gamma_mul_lt_exp_harmonic {n : ℕ} (hn : 0 < n) :
    Real.exp Real.eulerMascheroniConstant * (n : ℝ) < Real.exp (harmonic n : ℝ) := by
  have h := Real.exp_lt_exp.mpr (log_add_gamma_lt_harmonic hn)
  rw [Real.exp_add, Real.exp_log (by exact_mod_cast hn : (0 : ℝ) < n)] at h
  simpa [mul_comm] using h

lemma exp_harmonic_lt_exp_gamma_mul_add_one (n : ℕ) :
    Real.exp (harmonic n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * ((n : ℝ) + 1) := by
  have h := Real.exp_lt_exp.mpr (harmonic_lt_log_add_one_add_gamma n)
  rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h
  simpa [mul_comm] using h

lemma exp_gamma_lt_three : Real.exp Real.eulerMascheroniConstant < 3 := by
  have hgamma : Real.eulerMascheroniConstant < 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  exact (Real.exp_lt_exp.mpr hgamma).trans Real.exp_one_lt_three

lemma one_lt_log {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log (n : ℝ) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (Real.lt_log_iff_exp_lt (by linarith : 0 < (n : ℝ))).2
  exact Real.exp_one_lt_three.trans_le hnR

lemma log_log_nonneg {n : ℕ} (hn : 3 ≤ n) :
    0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg (one_lt_log hn).le

/-- Lagarias, Lemma 3.1. -/
lemma robinBound_le_exp_harmonic_mul_log_harmonic {n : ℕ} (hn : 3 ≤ n) :
    robinBound n ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith [one_lt_log hn]
  have hlog : Real.log (Real.log (n : ℝ)) ≤ Real.log (harmonic n : ℝ) :=
    Real.log_le_log hlogpos (log_lt_harmonic hnpos).le
  exact mul_le_mul (exp_gamma_mul_lt_exp_harmonic hnpos).le hlog
    (log_log_nonneg hn) (Real.exp_pos _).le

lemma robinBound_lt_rhs {n : ℕ} (hn : 3 ≤ n) : robinBound n < rhs n := by
  have h := robinBound_le_exp_harmonic_mul_log_harmonic hn
  have hpos := harmonic_pos (show 0 < n by omega)
  dsimp [rhs]
  linarith

lemma robinBound_le_bound {n : ℕ} (hn : 3 ≤ n) : robinBound n ≤ bound n :=
  (robinBound_lt_rhs hn).le

@[simp] lemma rhs_one : rhs 1 = 1 := by
  norm_num [rhs, harmonic_succ]

lemma rhs_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : rhs a ≤ rhs b := by
  have hH := harmonic_monotone_real hab
  unfold rhs
  exact add_le_add hH
    (mul_le_mul (Real.exp_le_exp.mpr hH)
      (Real.log_le_log (harmonic_pos ha) hH)
      (Real.log_nonneg (one_le_harmonic_real ha)) (Real.exp_pos _).le)

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

end LeanEval.NumberTheory.Lagarias
