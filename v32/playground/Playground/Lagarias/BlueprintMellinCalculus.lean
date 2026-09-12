import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Calculus for truncated Mellin transforms

The transform convention is exactly `integral_a^infinity f(x) x^(-s-1)`.
All analytic conclusions concern that defining integral. Polynomial bounds
and a positive distance from the convergence boundary justify differentiation;
no analytic continuation is postulated.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set Asymptotics
open scoped Topology

noncomputable def mellinCutoff (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (Ioi a).indicator f

noncomputable def truncatedMellin (a : ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin (mellinCutoff a f) (-s)

noncomputable def logWeight (f : ℝ → ℂ) (x : ℝ) : ℂ := (Real.log x : ℂ) * f x

lemma truncatedMellin_eq_integral {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℂ) (s : ℂ) :
    truncatedMellin a f s = ∫ x : ℝ in Ioi a, f x * (x : ℂ) ^ (-s - 1) := by
  unfold truncatedMellin mellin
  simp only [smul_eq_mul]
  calc
    _ = ∫ x : ℝ in Ioi 0, (Ioi a).indicator (fun x : ℝ => (x : ℂ) ^ (-s - 1) * f x) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      by_cases hxa : a < x <;> simp [mellinCutoff, hxa]
    _ = ∫ x : ℝ in Ioi a, (x : ℂ) ^ (-s - 1) * f x := by
      rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi ha)]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact mul_comm _ _

@[fun_prop] lemma measurable_mellinCutoff {a : ℝ} {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (mellinCutoff a f) := hf.indicator measurableSet_Ioi

@[fun_prop] lemma measurable_logWeight {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (logWeight f) := by
  unfold logWeight
  fun_prop

lemma locallyIntegrableOn_mellinCutoff {a C r : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hf : Measurable f) (hbound : ∀ x : ℝ, a < x → ‖f x‖ ≤ C * x ^ r) :
    LocallyIntegrableOn (mellinCutoff a f) (Ioi 0) := by
  have hc : Continuous (fun x : ℝ => C * (max a x) ^ r) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hmax : max a x ≠ 0 := (zero_lt_one.trans_le (ha.trans (le_max_left _ _))).ne'
    fun_prop (disch := assumption)
  apply (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi).mono
    (measurable_mellinCutoff hf).aestronglyMeasurable
  filter_upwards with x
  by_cases hx : a < x
  · have hx0 : 0 ≤ x := le_trans (by linarith : 0 ≤ a) hx.le
    have heq : mellinCutoff a f x = f x := by simp [mellinCutoff, hx]
    change ‖mellinCutoff a f x‖ ≤ ‖C * (max a x) ^ r‖
    rw [heq, max_eq_right hx.le, Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hx0 r))]
    exact hbound x hx
  · have heq : mellinCutoff a f x = 0 := by simp [mellinCutoff, hx]
    change ‖mellinCutoff a f x‖ ≤ ‖C * (max a x) ^ r‖
    rw [heq, norm_zero]
    exact norm_nonneg _

lemma mellinCutoff_isBigO_atTop {a C r : ℝ} (ha : 1 ≤ a)
    {f : ℝ → ℂ} (hbound : ∀ x : ℝ, a < x → ‖f x‖ ≤ C * x ^ r) :
    mellinCutoff a f =O[atTop] (fun x : ℝ => x ^ r) := by
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_gt_atTop a] with x hx
  have hx0 : 0 ≤ x := le_trans (by linarith : 0 ≤ a) hx.le
  have heq : mellinCutoff a f x = f x := by simp [mellinCutoff, hx]
  rw [heq, Real.norm_of_nonneg (Real.rpow_nonneg hx0 r)]
  exact hbound x hx

lemma mellinCutoff_isBigO_atZero {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (b : ℝ) :
    mellinCutoff a f =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 0, x < a := nhdsWithin_le_nhds (Iio_mem_nhds ha)
  filter_upwards [hsmall] with x hx
  simp [mellinCutoff, not_lt_of_ge hx.le]

lemma logWeight_mellinCutoff (a : ℝ) (f : ℝ → ℂ) :
    (fun x : ℝ => Real.log x • mellinCutoff a f x) = mellinCutoff a (logWeight f) := by
  funext x
  by_cases hx : a < x <;> simp [mellinCutoff, logWeight, hx, Complex.real_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Differentiation multiplies the integrand by `-log x`. -/
theorem hasDerivAt_truncatedMellin {a C r : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hf : Measurable f) (hbound : ∀ x : ℝ, a < x → ‖f x‖ ≤ C * x ^ r)
    {s : ℂ} (hs : r < s.re) :
    HasDerivAt (truncatedMellin a f) (-truncatedMellin a (logWeight f) s) s := by
  have hm := mellin_hasDerivAt_of_isBigO_rpow
    (a := -r) (b := -s.re - 1) (s := -s)
    (locallyIntegrableOn_mellinCutoff ha hC hf hbound)
    (by simpa only [neg_neg] using mellinCutoff_isBigO_atTop ha hbound)
    (by simp only [Complex.neg_re]; linarith)
    (mellinCutoff_isBigO_atZero (by linarith : 0 < a) f (-s.re - 1))
    (by simp only [Complex.neg_re]; linarith)
  rw [logWeight_mellinCutoff] at hm
  convert! hm.2.comp s (hasDerivAt_neg' s) using 1 <;>
    simp only [truncatedMellin, Function.comp_def, mul_neg_one]

/-- The defining integral is analytic throughout its convergence half-plane. -/
theorem analyticAt_truncatedMellin {a C r : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hf : Measurable f) (hbound : ∀ x : ℝ, a < x → ‖f x‖ ≤ C * x ^ r)
    {s : ℂ} (hs : r < s.re) : AnalyticAt ℂ (truncatedMellin a f) s := by
  have hd : DifferentiableOn ℂ (truncatedMellin a f) {z : ℂ | r < z.re} :=
    fun z hz => (hasDerivAt_truncatedMellin ha hC hf hbound hz).differentiableAt.differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

lemma logWeight_bound {a C r ε : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C) (hε : 0 < ε)
    {f : ℝ → ℂ} (hbound : ∀ x : ℝ, a < x → ‖f x‖ ≤ C * x ^ r) :
    ∀ x : ℝ, a < x → ‖logWeight f x‖ ≤ (C / ε) * x ^ (r + ε) := by
  intro x hx
  have hx1 : 1 ≤ x := ha.trans hx.le
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  unfold logWeight
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl]
  calc
    Real.log x * ‖f x‖ ≤ (x ^ ε / ε) * (C * x ^ r) :=
      mul_le_mul (Real.log_le_rpow_div hx0.le hε) (hbound x hx) (norm_nonneg _) (by positivity)
    _ = (C / ε) * x ^ (r + ε) := by
      rw [Real.rpow_add hx0]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- Two derivatives remove the two logarithmic denominators in the blueprint kernel. -/
theorem hasDerivAt_deriv_truncatedMellin {a C r : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hf : Measurable f) (hbound : ∀ x : ℝ, a < x → ‖f x‖ ≤ C * x ^ r)
    {s : ℂ} (hs : r < s.re) :
    HasDerivAt (deriv (truncatedMellin a f)) (truncatedMellin a (logWeight (logWeight f)) s) s := by
  let ε : ℝ := (s.re - r) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlog := hasDerivAt_truncatedMellin ha (div_nonneg hC hε.le)
    (measurable_logWeight hf) (logWeight_bound ha hC hε hbound)
    (s := s) (by dsimp [ε]; linarith)
  have hneg : HasDerivAt (fun z : ℂ => -truncatedMellin a (logWeight f) z)
      (truncatedMellin a (logWeight (logWeight f)) s) s := by
    convert! hlog.neg using 1 <;> simp only [neg_neg]
  apply hneg.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact (hasDerivAt_truncatedMellin ha hC hf hbound hz).deriv

end LeanEval.NumberTheory.Lagarias.Blueprint
