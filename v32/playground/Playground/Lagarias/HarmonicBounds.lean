import Playground.Lagarias.Bounds

/-!
# A uniform upper error bound for Lagarias' criterion

We prove `rhs n ≤ robinBound n + 16 * n / log n` for `n ≥ 3`.
This complements the constant-7 estimate for `n ≥ 27` in `Bounds`.
A quadratic Taylor lower bound controls all smaller error terms.
-/

namespace LeanEval.NumberTheory.Lagarias

lemma log_sq_le_two_mul {n : ℕ} (hn : 0 < n) :
    (Real.log (n : ℝ)) ^ 2 ≤ 2 * (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have h := Real.sum_le_exp_of_nonneg hlog 3
  norm_num [Finset.sum_range_succ, Nat.factorial_succ] at h
  rw [Real.exp_log hnR] at h
  nlinarith

/-- An explicit uniform `O(n / log n)` estimate. -/
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
