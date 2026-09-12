import Playground.Lagarias.Landau
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The integral version of Landau's positivity argument

These lemmas establish genuine integrability, not just equalities between
possibly undefined Bochner integrals. They will be used for the Laplace/Mellin
transforms of error terms in the oscillation argument.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open MeasureTheory Filter
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A nonnegative series of integrable functions with summable integrals has an
integrable pointwise sum. No measurability assumption on the limit is needed. -/
theorem integrable_of_nonneg_series {F : ℕ → α → ℝ} {g : α → ℝ}
    (hF0 : ∀ k a, 0 ≤ F k a) (hFi : ∀ k, Integrable (F k) μ)
    (hFs : Summable (fun k => ∫ a, F k a ∂μ))
    (hFg : ∀ a, HasSum (fun k => F k a) (g a)) :
    Integrable g μ := by
  have hnorm : Summable (fun k => ∫ a, ‖F k a‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hF0 _ _)] using hFs
  have heq : (∑' k, ∫ a, F k a ∂μ) = ∫ a, g a ∂μ := by
    rw [(hasSum_integral_of_summable_integral_norm hFi hnorm).tsum_eq]
    exact integral_congr_ae (ae_of_all _ fun a => (hFg a).tsum_eq)
  by_cases hg : (∫ a, g a ∂μ) = 0
  · have hzero (k : ℕ) : F k =ᵐ[μ] 0 := by
      apply (integral_eq_zero_iff_of_nonneg (hF0 k) (hFi k)).mp
      apply le_antisymm _ (integral_nonneg (hF0 k))
      calc
        (∫ a, F k a ∂μ) ≤ ∑' j, ∫ a, F j a ∂μ :=
          hFs.le_tsum k (fun j _ => integral_nonneg (hF0 j))
        _ = 0 := heq.trans hg
    have hgz : g =ᵐ[μ] 0 := by
      filter_upwards [ae_all_iff.mpr hzero] with a ha
      have hsum : HasSum (fun k => F k a) 0 := by
        simpa [ha] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
      exact (hFg a).unique hsum
    exact (integrable_zero : Integrable (fun _ : α => (0 : ℝ)) μ).congr hgz.symm
  · by_contra hnot
    exact hg (integral_undef hnot)

/-- The integral Tonelli step: summable nonnegative exponential moments force
integrability after exponential reweighting. -/
theorem integrable_weighted_exp_of_moments {w x : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hx : ∀ a, 0 ≤ x a)
    (hm : ∀ k : ℕ, Integrable (fun a => w a * x a ^ k) μ)
    (hs : Summable (fun k : ℕ => (∫ a, w a * x a ^ k ∂μ) / (k.factorial : ℝ))) :
    Integrable (fun a => w a * Real.exp (x a)) μ := by
  let F : ℕ → α → ℝ := fun k a => w a * x a ^ k / (k.factorial : ℝ)
  apply integrable_of_nonneg_series (F := F)
  · intro k a
    exact div_nonneg (mul_nonneg (hw a) (pow_nonneg (hx a) k)) (Nat.cast_nonneg _)
  · intro k
    exact (hm k).div_const (k.factorial : ℝ)
  · simpa only [F, integral_div] using hs
  · intro a
    have h := (NormedSpace.expSeries_div_hasSum_exp (x a)).mul_left (w a)
    simpa only [F, mul_div_assoc, ← Real.exp_eq_exp_ℝ] using h

/-- The corresponding exponential generating series computes the reweighted integral. -/
theorem hasSum_integral_weighted_exp {w x : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hx : ∀ a, 0 ≤ x a)
    (hm : ∀ k : ℕ, Integrable (fun a => w a * x a ^ k) μ)
    (hs : Summable (fun k : ℕ => (∫ a, w a * x a ^ k ∂μ) / (k.factorial : ℝ))) :
    HasSum (fun k : ℕ => (∫ a, w a * x a ^ k ∂μ) / (k.factorial : ℝ))
      (∫ a, w a * Real.exp (x a) ∂μ) := by
  let F : ℕ → α → ℝ := fun k a => w a * x a ^ k / (k.factorial : ℝ)
  have hF0 (k : ℕ) (a : α) : 0 ≤ F k a := by
    exact div_nonneg (mul_nonneg (hw a) (pow_nonneg (hx a) k)) (Nat.cast_nonneg _)
  have hFi (k : ℕ) : Integrable (F k) μ := (hm k).div_const (k.factorial : ℝ)
  have hnorm : Summable (fun k => ∫ a, ‖F k a‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hF0 _ _), F, integral_div] using hs
  have heq (a : α) : (∑' k, F k a) = w a * Real.exp (x a) := by
    simp only [F, mul_div_assoc, tsum_mul_left]
    rw [Real.exp_eq_exp_ℝ, (NormedSpace.expSeries_div_hasSum_exp (x a)).tsum_eq]
  simpa only [F, integral_div, heq] using
    hasSum_integral_of_summable_integral_norm hFi hnorm

end LeanEval.NumberTheory.Lagarias.Landau
