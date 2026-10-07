import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Comparing the two error terms in Lagarias' argument

This module proves the asymptotic comparison used after Robin's oscillation
result. It does not assume or prove any relation between divisor sums and zeros
of the zeta function. In particular, the comparison is not a replacement for
Robin's theorem.
-/

namespace LeanEval.NumberTheory.Lagarias

open Filter

/-- Any error of order `n / log n` is eventually strictly smaller than
Robin's positive oscillation term. The analytic comparison only needs `β < 1`,
not the stronger restriction `β < 1/2` supplied by Robin's theorem. -/
theorem eventually_error_lt_oscillation {C β : ℝ} (hC : 0 < C) (hβ : β < 1)
    (K : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      K * (n : ℝ) / Real.log (n : ℝ) <
        C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (1 - β)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hβ)).comp hlog
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [hpow.eventually_gt_atTop (K / C),
      hloglog.eventually_ge_atTop 1, hlog.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℕ)] with n hnPow hnLogLog hnLog hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (Real.log (n : ℝ)) ^ (1 - β) := Real.rpow_pos_of_pos hnLog _
  have hmain : K < C * (Real.log (n : ℝ)) ^ (1 - β) := by
    have h := (div_lt_iff₀ hC).mp hnPow
    nlinarith
  have hproduct : C * (Real.log (n : ℝ)) ^ (1 - β) ≤
      C * Real.log (Real.log (n : ℝ)) * (Real.log (n : ℝ)) ^ (1 - β) := by
    calc
      C * (Real.log (n : ℝ)) ^ (1 - β) =
          (C * (Real.log (n : ℝ)) ^ (1 - β)) * 1 := by ring
      _ ≤ (C * (Real.log (n : ℝ)) ^ (1 - β)) * Real.log (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hnLogLog (mul_nonneg hC.le hp.le)
      _ = _ := by ring
  calc
    K * (n : ℝ) / Real.log (n : ℝ) = ((n : ℝ) / Real.log (n : ℝ)) * K := by ring
    _ < ((n : ℝ) / Real.log (n : ℝ)) *
        (C * Real.log (Real.log (n : ℝ)) * (Real.log (n : ℝ)) ^ (1 - β)) :=
      mul_lt_mul_of_pos_left (hmain.trans_le hproduct) (div_pos hnR hnLog)
    _ = C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β := by
      rw [Real.rpow_sub hnLog, Real.rpow_one]
      field_simp [ne_of_gt hnLog]
      <;> ring

/-- The comparison also holds above any prescribed integer threshold. -/
theorem exists_threshold_error_lt_oscillation {C β : ℝ}
    (hC : 0 < C) (hβ : β < 1) (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K * (n : ℝ) / Real.log (n : ℝ) <
        C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β := by
  exact eventually_atTop.mp (eventually_error_lt_oscillation hC hβ K)

end LeanEval.NumberTheory.Lagarias
