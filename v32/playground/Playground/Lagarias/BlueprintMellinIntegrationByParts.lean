import Playground.Lagarias.BlueprintMellinDensities
import Playground.Lagarias.BlueprintJRightDerivative
import Mathlib.Tactic.LinearCombination

/-!
# Integration by parts for the actual smoothed transform

Blueprint: equation (10.6). Right derivatives handle every prime-power
endpoint, and absolute convergence plus an explicit vanishing boundary term
justify passage from finite intervals to the infinite Mellin integrals.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma mul_mellin_kernel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  calc
    _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-s - 1) := by rw [Complex.cpow_one]
    _ = (x : ℂ) ^ (1 + (-s - 1)) := (Complex.cpow_add 1 (-s - 1) hxC).symm
    _ = _ := by congr 1; ring

lemma smoothingDensity_mul_kernel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    smoothingDensity x * (x : ℂ) ^ (-s - 1) = ((R x * w x : ℝ) : ℂ) * (x : ℂ) ^ (-s) := by
  unfold smoothingDensity
  push_cast
  rw [← mul_mellin_kernel hx s]
  ring

lemma continuousOn_ofReal_cpow {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (r : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ r) (uIcc a b) := by
  by_cases hr : r = 0
  · subst r
    simpa only [Complex.cpow_zero] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℂ)) (uIcc a b))
  · intro x hx
    have hx2 : 2 ≤ x := (le_min ha hb).trans hx.1
    exact (hasDerivAt_ofReal_cpow_const (by linarith : x ≠ 0) hr).continuousAt.continuousWithinAt

set_option backward.isDefEq.respectTransparency false in
/-- The finite-interval identity is valid without differentiating through a prime-power jump. -/
lemma integral_smoothingDensity_kernel {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    {s : ℂ} (hs : s ≠ 0) :
    (∫ x : ℝ in a..b, smoothingDensity x * (x : ℂ) ^ (-s - 1)) =
      (J a : ℂ) * (a : ℂ) ^ (-s) - (J b : ℂ) * (b : ℂ) ^ (-s) -
        s * ∫ x : ℝ in a..b, (J x : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have hu : ContinuousOn J (uIcc a b) := continuousOn_J_interval ha hb
  have hv := continuousOn_ofReal_cpow ha hb (-s)
  have hu' : IntervalIntegrable (fun x : ℝ => -(R x * w x)) volume a b :=
    (intervalIntegrable_R_w ha hb).neg
  have hv' : IntervalIntegrable (fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1)) volume a b :=
    (continuousOn_const.mul (continuousOn_ofReal_cpow ha hb (-s - 1))).intervalIntegrable
  have hIBP := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right hu hv
    (fun x hx => hasDerivWithinAt_J_right ((le_min ha hb).trans hx.1.le))
    (fun x hx => (hasDerivAt_ofReal_cpow_const
      (show x ≠ 0 by have := (le_min ha hb).trans hx.1.le; linarith)
      (neg_ne_zero.mpr hs)).hasDerivWithinAt) hu' hv'
  have hleft : (∫ x : ℝ in a..b, J x • ((-s) * (x : ℂ) ^ (-s - 1))) =
      (-s) * ∫ x : ℝ in a..b, (J x : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    change J x • ((-s) * (x : ℂ) ^ (-s - 1)) = (-s) * ((J x : ℂ) * (x : ℂ) ^ (-s - 1))
    rw [Complex.real_smul]
    ring
  have hright : (∫ x : ℝ in a..b, (-(R x * w x)) • (x : ℂ) ^ (-s)) =
      -(∫ x : ℝ in a..b, smoothingDensity x * (x : ℂ) ^ (-s - 1)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ((le_min ha hb).trans hx.1)
    change (-(R x * w x)) • (x : ℂ) ^ (-s) = -(smoothingDensity x * (x : ℂ) ^ (-s - 1))
    rw [Complex.real_smul, smoothingDensity_mul_kernel hx0 s]
    push_cast
    ring
  rw [hleft, hright] at hIBP
  simp only [Complex.real_smul] at hIBP
  linear_combination -hIBP

lemma tendsto_J_cpow_boundary {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (J x : ℂ) * (x : ℂ) ^ (-s)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖(J x : ℂ) * (x : ℂ) ^ (-s)‖ ≤ (22 / Real.log 2) * x ^ (-s.re) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (abs_J_le_uniform hx) (Real.rpow_nonneg hx0.le _)
  apply squeeze_zero_norm' hbound
  simpa only [mul_zero] using (tendsto_rpow_neg_atTop hs).const_mul (22 / Real.log 2)

/-- Equation (10.6) for the actual transforms, with the boundary term justified. -/
theorem WIntegral_eq_boundary {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    WIntegral a s = (a : ℂ) ^ (-s) * (J a : ℂ) - s * Jhat a s := by
  have ha0 : 0 ≤ a := by linarith
  have hs0 : s ≠ 0 := by
    intro heq
    rw [heq, Complex.zero_re] at hs
    exact (lt_irrefl (0 : ℝ)) hs
  have hWlim : Tendsto (fun b : ℝ => ∫ x : ℝ in a..b,
      smoothingDensity x * (x : ℂ) ^ (-s - 1)) atTop (𝓝 (WIntegral a s)) := by
    simpa only [WIntegral, truncatedMellin_eq_integral ha0] using
      intervalIntegral_tendsto_integral_Ioi a (integrableOn_WIntegral ha hs) tendsto_id
  have hJlim : Tendsto (fun b : ℝ => ∫ x : ℝ in a..b,
      (J x : ℂ) * (x : ℂ) ^ (-s - 1)) atTop (𝓝 (Jhat a s)) := by
    simpa only [Jhat, truncatedMellin_eq_integral ha0] using
      intervalIntegral_tendsto_integral_Ioi a (integrableOn_Jhat ha hs) tendsto_id
  have hRlim := ((tendsto_const_nhds.sub (tendsto_J_cpow_boundary hs)).sub (hJlim.const_mul s))
  have heq : (fun b : ℝ => ∫ x : ℝ in a..b, smoothingDensity x * (x : ℂ) ^ (-s - 1)) =ᶠ[atTop]
      (fun b : ℝ => (J a : ℂ) * (a : ℂ) ^ (-s) - (J b : ℂ) * (b : ℂ) ^ (-s) -
        s * ∫ x : ℝ in a..b, (J x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with b hb
    exact integral_smoothingDensity_kernel ha hb hs0
  rw [Filter.tendsto_congr' heq] at hWlim
  have hvalue : WIntegral a s = (J a : ℂ) * (a : ℂ) ^ (-s) - s * Jhat a s := by
    simpa only [sub_zero] using tendsto_nhds_unique hWlim hRlim
  calc
    WIntegral a s = (J a : ℂ) * (a : ℂ) ^ (-s) - s * Jhat a s := hvalue
    _ = _ := by ring

end LeanEval.NumberTheory.Lagarias.Blueprint
