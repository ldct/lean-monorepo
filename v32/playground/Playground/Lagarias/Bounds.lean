import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# Elementary bounds for the Lagarias criterion

These lemmas do not assume the Riemann hypothesis or any form of Robin's theorem.
The lower comparison is Lemma 3.1 of Lagarias, arXiv:math/0008177.

This module is intentionally independent of `v32/Lagarias.lean`, whose final
RH equivalence is still incomplete. See `v32/LAGARIAS.md` for verification status.
-/

namespace LeanEval.NumberTheory.Lagarias

/-- The right-hand side of the elementary Lagarias inequality. -/
noncomputable def rhs (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- The comparison function occurring in Robin's theorem. -/
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

/-- An explicit one-sided error estimate, obtained without Euler--Maclaurin. -/
lemma harmonic_lt_log_add_gamma_add_inv {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) <
      Real.log (n : ℝ) + Real.eulerMascheroniConstant + 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos
    (show 0 < ((n : ℝ) + 1) / (n : ℝ) by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hnR)] at h
  have hdiv : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
    rw [add_div, div_self (ne_of_gt hnR)]
    ring
  rw [hdiv] at h
  linarith [harmonic_lt_log_add_one_add_gamma n]

lemma harmonic_pos {n : ℕ} (hn : 0 < n) : 0 < (harmonic n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  linarith [log_add_gamma_lt_harmonic hn, gamma_pos]

lemma harmonic_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (harmonic_pos hn).le

lemma one_lt_log {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log (n : ℝ) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (Real.lt_log_iff_exp_lt (by linarith : 0 < (n : ℝ))).2
  exact Real.exp_one_lt_three.trans_le hnR

/-- Lagarias, Lemma 3.1: the exponential-logarithmic term dominates Robin's bound. -/
lemma robinBound_le_exp_harmonic_mul_log_harmonic {n : ℕ} (hn : 3 ≤ n) :
    robinBound n ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hH := log_add_gamma_lt_harmonic hnpos
  have hlogn := one_lt_log hn
  have hlogH : Real.log (Real.log (n : ℝ)) ≤ Real.log (harmonic n : ℝ) := by
    apply Real.log_le_log (by linarith : 0 < Real.log (n : ℝ))
    linarith [gamma_pos]
  have hexp : Real.exp Real.eulerMascheroniConstant * (n : ℝ) ≤
      Real.exp (harmonic n : ℝ) := by
    calc
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) =
          Real.exp (Real.log (n : ℝ) + Real.eulerMascheroniConstant) := by
            rw [Real.exp_add, Real.exp_log hnR]
            ring
      _ ≤ Real.exp (harmonic n : ℝ) := Real.exp_le_exp.mpr hH.le
  exact mul_le_mul hexp hlogH (Real.log_nonneg hlogn.le) (Real.exp_pos _).le

lemma robinBound_lt_rhs {n : ℕ} (hn : 3 ≤ n) : robinBound n < rhs n := by
  have h := robinBound_le_exp_harmonic_mul_log_harmonic hn
  have hpos := harmonic_pos (show 0 < n by omega)
  dsimp [rhs]
  linarith

@[simp] lemma rhs_one : rhs 1 = 1 := by
  norm_num [rhs, harmonic_succ]

end LeanEval.NumberTheory.Lagarias
