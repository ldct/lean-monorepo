import Playground.Lagarias.BlueprintMertensFirst
import Playground.Lagarias.BlueprintPrimePowerSum
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The prime-power Mertens limit before identifying its constant

Blueprint: Lemma 3.2, through equation (3.5). Abel summation and the proved
bounded first error give a constant and an explicit remainder at most
`14 / log x`. The identification of this constant with Euler's constant is
NOT presumed here: that is a separate essential theorem.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset MeasureTheory Filter
open scoped Topology ArithmeticFunction.vonMangoldt

noncomputable def mertensKernel (t : ℝ) : ℝ := t⁻¹ / (Real.log t) ^ 2

lemma mertensKernel_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ mertensKernel t := by
  unfold mertensKernel
  positivity

lemma measurable_mertensKernel : Measurable mertensKernel := by
  unfold mertensKernel
  fun_prop

lemma integrableOn_mertensKernel {x : ℝ} (hx : 1 < x) :
    IntegrableOn mertensKernel (Set.Ioi x) := integrableOn_inv_div_log_sq_Ioi hx

lemma integral_mertensKernel {x : ℝ} (hx : 1 < x) :
    (∫ t : ℝ in Set.Ioi x, mertensKernel t) = 1 / Real.log x := by
  simpa only [mertensKernel, one_div] using integral_inv_div_log_sq_Ioi hx

lemma integrableOn_firstError_kernel {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t => firstError t * mertensKernel t) (Set.Ioi x) := by
  have hmajor := (integrableOn_mertensKernel (by linarith : 1 < x)).const_mul (7 : ℝ)
  apply hmajor.mono' ((measurable_firstError.mul measurable_mertensKernel).aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht2 : 2 ≤ t := hx.trans ht.le
  have hk : 0 ≤ mertensKernel t := mertensKernel_nonneg (by linarith)
  change ‖firstError t * mertensKernel t‖ ≤ 7 * mertensKernel t
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hk]
  exact mul_le_mul_of_nonneg_right (abs_firstError_le_seven ht2) hk

lemma abs_integral_firstError_kernel_le {x : ℝ} (hx : 2 ≤ x) :
    |∫ t : ℝ in Set.Ioi x, firstError t * mertensKernel t| ≤ 7 / Real.log x := by
  have hmajor := (integrableOn_mertensKernel (by linarith : 1 < x)).const_mul (7 : ℝ)
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi x),
      ‖firstError t * mertensKernel t‖ ≤ 7 * mertensKernel t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change x < t at ht
    have hk := mertensKernel_nonneg (show 0 ≤ t by linarith)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hk]
    exact mul_le_mul_of_nonneg_right (abs_firstError_le_seven (by linarith)) hk
  have hh := norm_integral_le_of_norm_le hmajor hbound
  rw [integral_const_mul, integral_mertensKernel (by linarith : 1 < x)] at hh
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using hh

lemma sum_Icc_mangoldt_div (x : ℝ) :
    (∑ k ∈ Icc 0 ⌊x⌋₊, Λ k / (k : ℝ)) = A x := by
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  simp [A]

lemma sum_Icc_mangoldt_div_log (x : ℝ) :
    (∑ k ∈ Icc 0 ⌊x⌋₊, (Real.log (k : ℝ))⁻¹ * (Λ k / (k : ℝ))) = B x := by
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊), B_eq_sum_Ioc_vonMangoldt]
  simp only [Nat.cast_zero, div_zero, mul_zero, zero_add]
  apply sum_congr rfl
  intro k hk
  ring

/-- Abel summation with the logarithmic weight, including the endpoint at 2. -/
theorem B_eq_abel {x : ℝ} (hx : 2 ≤ x) :
    B x = A x / Real.log x + ∫ t : ℝ in 2..x, A t * mertensKernel t := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun t => (Real.log t)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1]) (by linarith [ht.1])
      (by linarith [ht.1])
  have hint : IntegrableOn (deriv (fun t : ℝ => (Real.log t)⁻¹)) (Set.Icc 2 x) := by
    rw [Real.deriv_inv_log]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hp0 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hl0
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun t : ℝ => -t⁻¹ / Real.log t ^ 2) t).continuousWithinAt
  have hab := sum_mul_eq_sub_integral_mul₁ (fun k : ℕ => Λ k / (k : ℝ))
    (by simp) (by simp) x hdiff hint
  rw [sum_Icc_mangoldt_div_log, sum_Icc_mangoldt_div] at hab
  simp_rw [Real.deriv_inv_log, sum_Icc_mangoldt_div] at hab
  rw [← intervalIntegral.integral_of_le hx] at hab
  have hfun : (fun t : ℝ => -t⁻¹ / Real.log t ^ 2 * A t) =
      (fun t => -(A t * mertensKernel t)) := by
    funext t
    unfold mertensKernel
    ring
  rw [hfun, intervalIntegral.integral_neg] at hab
  simpa [div_eq_mul_inv, mul_comm] using hab

lemma intervalIntegrable_h {x : ℝ} (hx : 2 ≤ x) : IntervalIntegrable h volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  exact (hasDerivAt_h (by linarith [ht.1] : 1 < t)).continuousAt.continuousWithinAt

lemma integral_h {x : ℝ} (hx : 2 ≤ x) : (∫ t : ℝ in 2..x, h t) = g x - g 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (intervalIntegrable_h hx)
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  exact hasDerivAt_g (by linarith [ht.1])

lemma intervalIntegrable_firstError_kernel {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => firstError t * mertensKernel t) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact (integrableOn_firstError_kernel (x := 2) le_rfl).mono_set Set.Ioc_subset_Ioi_self

/-- The candidate Mertens constant, not yet identified as Euler's constant. -/
noncomputable def mertensConstant : ℝ :=
  1 - g 2 + ∫ t : ℝ in Set.Ioi 2, firstError t * mertensKernel t

noncomputable def secondError (x : ℝ) : ℝ := B x - g x - mertensConstant

/-- The exact integral remainder in equation (3.5). -/
theorem secondError_eq {x : ℝ} (hx : 2 ≤ x) :
    secondError x = firstError x / Real.log x -
      ∫ t : ℝ in Set.Ioi x, firstError t * mertensKernel t := by
  have hlogx : Real.log x ≠ 0 := (Real.log_pos (by linarith : 1 < x)).ne'
  have hsplit : (∫ t : ℝ in 2..x, A t * mertensKernel t) =
      (∫ t : ℝ in 2..x, h t) + ∫ t : ℝ in 2..x, firstError t * mertensKernel t := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_h hx)
      (intervalIntegrable_firstError_kernel hx)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlt : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    unfold firstError h mertensKernel
    field_simp
    ring
  have htail := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_firstError_kernel (x := 2) le_rfl) (integrableOn_firstError_kernel hx)
  unfold secondError mertensConstant
  rw [B_eq_abel hx, hsplit, integral_h hx]
  have hAx : A x / Real.log x = 1 + firstError x / Real.log x := by
    unfold firstError
    field_simp
    ring
  rw [hAx]
  linarith only [htail]

/-- An explicit modulus of the prime-power Mertens limit. -/
theorem abs_secondError_le {x : ℝ} (hx : 2 ≤ x) : |secondError x| ≤ 14 / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [secondError_eq hx]
  calc
    |firstError x / Real.log x - ∫ t : ℝ in Set.Ioi x, firstError t * mertensKernel t| ≤
        |firstError x / Real.log x| + |∫ t : ℝ in Set.Ioi x, firstError t * mertensKernel t| :=
      abs_sub _ _
    _ ≤ 7 / Real.log x + 7 / Real.log x := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hlog]
        exact div_le_div_of_nonneg_right (abs_firstError_le_seven hx) hlog.le
      · exact abs_integral_firstError_kernel_le hx
    _ = 14 / Real.log x := by ring

/-- Convergence is proved before the value of the limiting constant is identified. -/
theorem tendsto_secondError : Tendsto secondError atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_ge_atTop (2 : ℝ) |>.mono fun x hx => ?_)
    (show Tendsto (fun x : ℝ => 14 / Real.log x) atTop (𝓝 0) by
      simpa [div_eq_mul_inv] using Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (14 : ℝ))
  simpa only [Real.norm_eq_abs] using abs_secondError_le hx

end LeanEval.NumberTheory.Lagarias.Blueprint
