import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Harmonic estimates for Lagarias' criterion

These lemmas use Mathlib's definition of Euler's constant. In particular, no
identification with a separately postulated constant is assumed.

Reference: Lagarias, arXiv:math/0008177, Lemma 3.1.
-/

namespace LeanEval.NumberTheory.Lagarias

/-- The right-hand side of Lagarias' elementary inequality. -/
noncomputable def bound (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- The main term in Robin's divisor-sum estimate. -/
noncomputable def robinBound (n : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))

lemma gamma_pos : 0 < Real.eulerMascheroniConstant := by
  linarith [Real.one_half_lt_eulerMascheroniConstant]

lemma harmonic_nonneg_real (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  have h : (0 : ℚ) ≤ harmonic n := by
    unfold harmonic
    positivity
  exact_mod_cast h

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
  norm_num at h ⊢
  exact h

lemma log_add_gamma_lt_harmonic {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) + Real.eulerMascheroniConstant < (harmonic n : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', Nat.ne_of_gt hn, if_false] at h
  linarith

lemma harmonic_lt_log_add_one_add_gamma (n : ℕ) :
    (harmonic n : ℝ) < Real.log ((n : ℝ) + 1) + Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold Real.eulerMascheroniSeq at h
  linarith

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

lemma log_log_nonneg {n : ℕ} (hn : 3 ≤ n) :
    0 ≤ Real.log (Real.log (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : Real.exp 1 < (3 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hlog : 1 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 (he.trans_le (by exact_mod_cast hn))
  exact Real.log_nonneg hlog.le

/-- Lagarias, Lemma 3.1. -/
theorem robinBound_le_exp_harmonic_mul_log_harmonic {n : ℕ} (hn : 3 ≤ n) :
    robinBound n ≤ Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog : Real.log (Real.log (n : ℝ)) ≤ Real.log (harmonic n : ℝ) :=
    Real.log_le_log hlogpos (log_lt_harmonic hnpos).le
  unfold robinBound
  exact mul_le_mul (exp_gamma_mul_lt_exp_harmonic hnpos).le hlog
    (log_log_nonneg hn) (Real.exp_pos _).le

/-- Robin's main term lies below the full Lagarias right-hand side. -/
theorem robinBound_le_bound {n : ℕ} (hn : 3 ≤ n) : robinBound n ≤ bound n := by
  have h := robinBound_le_exp_harmonic_mul_log_harmonic hn
  have h0 := harmonic_nonneg_real n
  unfold bound
  linarith

end LeanEval.NumberTheory.Lagarias
