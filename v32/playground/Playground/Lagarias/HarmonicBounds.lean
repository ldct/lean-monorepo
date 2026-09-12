import Playground.Lagarias.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# An explicit upper error bound for Lagarias' criterion

We prove `rhs n ≤ robinBound n + 16 * n / log n` for `n ≥ 3`.
The constant is intentionally looser than Lagarias' Lemma 3.2: the reverse
implication uses the order of the error, not the optimized constant 7.

The shifted harmonic bound from Mathlib gives `exp H_n < exp gamma * (n + 1)`.
A quadratic Taylor lower bound for `exp` controls the remaining logarithms.
No numerical approximations, additional axioms, or RH assumptions are used.
-/

namespace LeanEval.NumberTheory.Lagarias

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

lemma log_sq_le_two_mul {n : ℕ} (hn : 0 < n) :
    (Real.log (n : ℝ)) ^ 2 ≤ 2 * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have h := Real.sum_le_exp_of_nonneg hlog 3
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  rw [Real.exp_log hnR] at h
  nlinarith

lemma log_harmonic_le_log_log_add_inv {n : ℕ} (hn : 3 ≤ n) :
    Real.log (harmonic n : ℝ) ≤
      Real.log (Real.log (n : ℝ)) + 1 / Real.log (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hL : 0 < Real.log (n : ℝ) := by linarith [one_lt_log hn]
  have hH : Real.log (harmonic n : ℝ) ≤ Real.log (Real.log (n : ℝ) + 1) := by
    apply Real.log_le_log (harmonic_pos hnpos)
    linarith [harmonic_le_one_add_log n]
  have h := Real.log_le_sub_one_of_pos
    (show 0 < (Real.log (n : ℝ) + 1) / Real.log (n : ℝ) by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hL)] at h
  have hdiv : (Real.log (n : ℝ) + 1) / Real.log (n : ℝ) - 1 =
      1 / Real.log (n : ℝ) := by
    rw [add_div, div_self (ne_of_gt hL)]
    ring
  rw [hdiv] at h
  linarith

/-- An explicit version of the `O(n / log n)` estimate needed in the reverse implication. -/
theorem rhs_le_robinBound_add_sixteen {n : ℕ} (hn : 3 ≤ n) :
    rhs n ≤ robinBound n + 16 * (n : ℝ) / Real.log (n : ℝ) := by
  let x : ℝ := n
  let L : ℝ := Real.log (n : ℝ)
  let E : ℝ := Real.exp Real.eulerMascheroniConstant
  have hnpos : 0 < n := by omega
  have hx : 1 ≤ x := by exact_mod_cast (show 1 ≤ n by omega)
  have hLone : 1 < L := one_lt_log hn
  have hL : 0 < L := by linarith
  have hEpos : 0 ≤ E := (Real.exp_pos _).le
  have hE : E ≤ 3 := exp_gamma_lt_three.le
  have hsq : L ^ 2 ≤ 2 * x := log_sq_le_two_mul hnpos
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hlogL : Real.log L ≤ L := by
    linarith [Real.log_le_sub_one_of_pos hL]
  have hLL : L * Real.log L ≤ L ^ 2 := by
    calc
      L * Real.log L ≤ L * L := mul_le_mul_of_nonneg_left hlogL hL.le
      _ = L ^ 2 := by ring
  have hELog : E * (L * Real.log L) ≤ 3 * L ^ 2 := by
    calc
      E * (L * Real.log L) ≤ E * L ^ 2 := mul_le_mul_of_nonneg_left hLL hEpos
      _ ≤ 3 * L ^ 2 := mul_le_mul_of_nonneg_right hE (sq_nonneg L)
  have hEx : E * (x + 1) ≤ 6 * x := by
    calc
      E * (x + 1) ≤ 3 * (x + 1) := mul_le_mul_of_nonneg_right hE (by linarith)
      _ ≤ 6 * x := by linarith
  have hnum : (L ^ 2 + L) + E * (L * Real.log L) + E * (x + 1) ≤ 16 * x := by
    nlinarith
  have hupper : rhs n ≤ (L + 1) + E * (x + 1) * (Real.log L + 1 / L) := by
    unfold rhs
    apply add_le_add
    · change (harmonic n : ℝ) ≤ Real.log (n : ℝ) + 1
      linarith [harmonic_le_one_add_log n]
    · exact mul_le_mul (exp_harmonic_lt_exp_gamma_mul_add_one n).le
        (log_harmonic_le_log_log_add_inv hn)
        (Real.log_nonneg (one_le_harmonic_real hnpos)) (by positivity)
  have hexpand : (L + 1) + E * (x + 1) * (Real.log L + 1 / L) =
      robinBound n + ((L ^ 2 + L) + E * (L * Real.log L) + E * (x + 1)) / L := by
    change (L + 1) + E * (x + 1) * (Real.log L + 1 / L) =
      E * x * Real.log L + ((L ^ 2 + L) + E * (L * Real.log L) + E * (x + 1)) / L
    field_simp [ne_of_gt hL]
    <;> ring
  change rhs n ≤ robinBound n + 16 * x / L
  calc
    rhs n ≤ (L + 1) + E * (x + 1) * (Real.log L + 1 / L) := hupper
    _ = robinBound n + ((L ^ 2 + L) + E * (L * Real.log L) + E * (x + 1)) / L := hexpand
    _ ≤ robinBound n + 16 * x / L :=
      add_le_add_left (div_le_div_of_nonneg_right hnum hL.le) _

end LeanEval.NumberTheory.Lagarias
