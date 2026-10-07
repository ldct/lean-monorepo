import Playground.Lagarias.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparing the Lagarias error with Robin's oscillation term

The analysis in this file is elementary. In particular, it does NOT establish
that failure of RH produces the required divisor-sum oscillation. It proves
that any function with that oscillation eventually exceeds the Lagarias bound.

An explicit logarithmic threshold replaces limit/asymptotic notation:
`log n ≥ (8 / C)^2` and `n ≥ 27` suffice when `beta ≤ 1/2`.
-/

namespace LeanEval.NumberTheory.Lagarias

lemma seven_div_lt_oscillation_ratio {t C beta : ℝ}
    (ht : 3 ≤ t) (hC : 0 < C) (hbeta : beta ≤ 1 / 2)
    (hlarge : (8 / C) ^ 2 ≤ t) :
    7 / t < C * Real.log t / t ^ beta := by
  have ht0 : 0 < t := by linarith
  let q := t ^ (1 / 2 : ℝ)
  have hq0 : 0 < q := Real.rpow_pos_of_pos ht0 _
  have hq2 : q ^ 2 = t := by
    dsimp [q]
    rw [← Real.rpow_two, ← Real.rpow_mul ht0.le]
    norm_num
  have hqq : q * q = t := by nlinarith only [hq2]
  have hqBound : 8 / C ≤ q := by
    have h8 : 0 < 8 / C := by positivity
    nlinarith only [hlarge, hq2, hq0, h8]
  have hCq : 7 < C * q := by
    have h := (div_le_iff₀ hC).mp hqBound
    nlinarith only [h]
  have hlog : 1 ≤ Real.log t :=
    (Real.le_log_iff_exp_le ht0).2 (Real.exp_one_lt_three.le.trans ht)
  have hpower : t ^ beta ≤ q :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ t) hbeta
  have hpower0 : 0 < t ^ beta := Real.rpow_pos_of_pos ht0 _
  have hmain : 7 / t < C / q := by
    apply (div_lt_div_iff₀ ht0 hq0).2
    have h := mul_lt_mul_of_pos_right hCq hq0
    simpa only [mul_assoc, hqq] using h
  calc
    7 / t < C / q := hmain
    _ ≤ C / t ^ beta := div_le_div_of_nonneg_left hC.le hpower0 hpower
    _ ≤ C * Real.log t / t ^ beta :=
      div_le_div_of_nonneg_right (by nlinarith only [hC, hlog]) hpower0.le

lemma error_lt_oscillation_of_log_large {n : ℕ} {C beta : ℝ}
    (hn : 27 ≤ n) (hC : 0 < C) (hbeta : beta ≤ 1 / 2)
    (hlarge : (8 / C) ^ 2 ≤ Real.log (n : ℝ)) :
    7 * (n : ℝ) / Real.log (n : ℝ) <
      C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ beta := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hratio := seven_div_lt_oscillation_ratio (three_lt_log hn).le hC hbeta hlarge
  calc
    7 * (n : ℝ) / Real.log (n : ℝ) =
        (n : ℝ) * (7 / Real.log (n : ℝ)) := by ring
    _ < (n : ℝ) *
        (C * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ beta) :=
      mul_lt_mul_of_pos_left hratio hnR
    _ = _ := by ring

/-- Robin's error term exceeds the proved elementary upper error for all large integers. -/
theorem exists_threshold_error_lt_oscillation {C beta : ℝ}
    (hC : 0 < C) (hbeta : beta ≤ 1 / 2) :
    ∃ N : ℕ, 27 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      7 * (n : ℝ) / Real.log (n : ℝ) <
        C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ beta := by
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp ((8 / C) ^ 2))
  refine ⟨max M 27, le_max_right _ _, ?_⟩
  intro n hn
  have hn27 : 27 ≤ n := (le_max_right M 27).trans hn
  have hMn : M ≤ n := (le_max_left M 27).trans hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hexp : Real.exp ((8 / C) ^ 2) < (n : ℝ) :=
    hM.trans_le (by exact_mod_cast hMn)
  have hlarge : (8 / C) ^ 2 ≤ Real.log (n : ℝ) :=
    ((Real.lt_log_iff_exp_lt hnR).2 hexp).le
  exact error_lt_oscillation_of_log_large hn27 hC hbeta hlarge

/-- A general transfer principle; the arithmetic oscillation is an explicit hypothesis. -/
theorem counterexamples_of_robin_oscillation {f : ℕ → ℝ} {C beta : ℝ}
    (hC : 0 < C) (hbeta : beta ≤ 1 / 2)
    (hosc : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      robinBound n + C * (n : ℝ) * Real.log (Real.log (n : ℝ)) /
        Real.log (n : ℝ) ^ beta ≤ f n) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ rhs n < f n := by
  obtain ⟨M, hM27, hM⟩ := exists_threshold_error_lt_oscillation hC hbeta
  intro N
  obtain ⟨n, hn, hfn⟩ := hosc (max M N)
  have hMn : M ≤ n := (le_max_left M N).trans hn
  have hNn : N ≤ n := (le_max_right M N).trans hn
  have hn27 : 27 ≤ n := hM27.trans hMn
  have hupper := rhs_le_robinBound_add_error hn27
  have herror := hM n hMn
  refine ⟨n, hNn, ?_⟩
  linarith only [hupper, herror, hfn]

end LeanEval.NumberTheory.Lagarias
