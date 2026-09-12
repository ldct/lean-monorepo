import Playground.Lagarias.LandauIntegral
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Landau's singularity argument for transform integrals

Mathlib's complex moment-generating function is defined for arbitrary measures,
not just probability measures. Thus this development applies to Laplace and
Mellin transforms after a change of variable or a change of density.

The theorem uses the actual transform and its proved derivative formulas. No
hypothesis identifying unproved Taylor coefficients is introduced.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℝ}

/-- Nonnegative transform arguments make the derivative norms exact positive moments. -/
lemma norm_iteratedDeriv_complexMGF_of_nonneg (hX : ∀ a, 0 ≤ X a)
    {s : ℝ} (hs : s ∈ interior (integrableExpSet X μ)) (k : ℕ) :
    ‖iteratedDeriv k (complexMGF X μ) (s : ℂ)‖ =
      ∫ a, Real.exp (s * X a) * X a ^ k ∂μ := by
  rw [iteratedDeriv_complexMGF (by simpa using hs) k]
  have heq : (∫ a, (X a : ℂ) ^ k * Complex.exp ((s : ℂ) * X a) ∂μ) =
      ((∫ a, X a ^ k * Real.exp (s * X a) ∂μ : ℝ) : ℂ) := by
    norm_cast
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun a =>
      mul_nonneg (pow_nonneg (hX a) k) (Real.exp_pos _).le))]
  apply integral_congr_ae
  exact ae_of_all _ fun a => mul_comm _ _

/-- A holomorphic continuation of a positive transform forces genuine convergence
at each real point to the right of the center inside its Taylor disc. -/
theorem integrable_exp_of_holomorphic_continuation (hX : ∀ a, 0 ≤ X a)
    {s r R : ℝ} (hs : s ∈ interior (integrableExpSet X μ))
    (hr : 0 ≤ r) (hrR : r < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball (s : ℂ) R))
    (heq : F =ᶠ[𝓝 (s : ℂ)] complexMGF X μ) :
    Integrable (fun a => Real.exp ((s + r) * X a)) μ := by
  have hzdist : ‖((s + r : ℝ) : ℂ) - (s : ℂ)‖ = r := by
    have harg : ((s + r : ℝ) : ℂ) - (s : ℂ) = (r : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hz : ((s + r : ℝ) : ℂ) ∈ Metric.ball (s : ℂ) R := by
    simpa only [Metric.mem_ball, dist_eq_norm, hzdist] using hrR
  have htaylor := Complex.hasSum_taylorSeries_on_ball hF hz
  have hnorm := summable_norm_iff.mpr htaylor.summable
  have hmoment (k : ℕ) :
      (∫ a, Real.exp (s * X a) * (r * X a) ^ k ∂μ) =
        r ^ k * ∫ a, Real.exp (s * X a) * X a ^ k ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun a => by dsimp only; rw [mul_pow]; ring
  have hcoeff (k : ℕ) :
      ‖(k.factorial : ℂ)⁻¹ • (((s + r : ℝ) : ℂ) - (s : ℂ)) ^ k •
        iteratedDeriv k F (s : ℂ)‖ =
      (∫ a, Real.exp (s * X a) * (r * X a) ^ k ∂μ) / (k.factorial : ℝ) := by
    rw [norm_smul, norm_smul, norm_inv, norm_pow, hzdist,
      heq.iteratedDeriv_eq k, norm_iteratedDeriv_complexMGF_of_nonneg hX hs k,
      Complex.norm_natCast, hmoment]
    ring
  have hpower : Summable (fun k : ℕ =>
      (∫ a, Real.exp (s * X a) * (r * X a) ^ k ∂μ) / (k.factorial : ℝ)) :=
    hnorm.congr hcoeff
  have hm (k : ℕ) : Integrable (fun a => Real.exp (s * X a) * (r * X a) ^ k) μ := by
    have h := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hs k).const_mul (r ^ k)
    apply h.congr
    exact ae_of_all _ fun a => by dsimp only; rw [mul_pow]; ring
  have hweighted := integrable_weighted_exp_of_moments
    (fun a => (Real.exp_pos (s * X a)).le) (fun a => mul_nonneg hr (hX a)) hm hpower
  simpa only [← Real.exp_add, ← add_mul] using hweighted

/-- Landau's theorem for an integral transform: a finite right boundary of
exponential integrability cannot admit a holomorphic continuation.

The two boundary hypotheses describe the convergence boundary directly; there
is no assumption that the measure is finite or normalized. -/
theorem no_holomorphic_extension_at_integrability_boundary (hX : ∀ a, 0 ≤ X a)
    {b : ℝ}
    (hbelow : ∀ t : ℝ, t < b → t ∈ integrableExpSet X μ)
    (habove : ∀ t : ℝ, b < t → t ∉ integrableExpSet X μ)
    {F : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : DifferentiableOn ℂ F (Metric.ball (b : ℂ) δ))
    (heq : ∀ z ∈ Metric.ball (b : ℂ) δ, z.re < b → F z = complexMGF X μ z) : False := by
  let s : ℝ := b - δ / 4
  have hsb : s < b := by dsimp [s]; linarith
  have hsc : dist (s : ℂ) (b : ℂ) = δ / 4 := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hdiff : s - b = -(δ / 4) := by dsimp [s]; ring
    rw [hdiff, abs_neg, abs_of_nonneg (by positivity : 0 ≤ δ / 4)]
  have hsBall : (s : ℂ) ∈ Metric.ball (b : ℂ) δ := by
    rw [Metric.mem_ball, hsc]
    linarith
  have hsub : Metric.ball (s : ℂ) (δ / 2) ⊆ Metric.ball (b : ℂ) δ :=
    Metric.ball_subset_ball' (by rw [hsc]; linarith)
  have heq' : F =ᶠ[𝓝 (s : ℂ)] complexMGF X μ := by
    have hb : ∀ᶠ z in 𝓝 (s : ℂ), z ∈ Metric.ball (b : ℂ) δ :=
      Metric.isOpen_ball.mem_nhds hsBall
    have hr : ∀ᶠ z : ℂ in 𝓝 (s : ℂ), z.re < b :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hsb
    filter_upwards [hb, hr] with z hzb hzr using heq z hzb hzr
  have hs : s ∈ interior (integrableExpSet X μ) := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Iio_mem_nhds hsb) (fun t ht => hbelow t ht)
  have hconv := integrable_exp_of_holomorphic_continuation hX
    (s := s) (r := δ / 3) (R := δ / 2) hs (by positivity) (by linarith)
    (hF.mono hsub) heq'
  exact habove (s + δ / 3) (by dsimp [s]; linarith) hconv

/-- For a nonnegative measurable argument, exponential integrability is downward closed. -/
lemma integrable_exp_of_le (hXm : AEMeasurable X μ) (hX : ∀ a, 0 ≤ X a)
    {s t : ℝ} (hst : s ≤ t) (ht : t ∈ integrableExpSet X μ) :
    s ∈ integrableExpSet X μ := by
  change Integrable (fun a => Real.exp (s * X a)) μ
  have ht' : Integrable (fun a => Real.exp (t * X a)) μ := ht
  apply ht'.mono' (Real.measurable_exp.comp_aemeasurable (hXm.const_mul s)).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    dsimp only
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hst (hX a))

/-- The convergence boundary is an actual singularity, with no separate boundary
hypotheses: it is defined as the supremum of the nonempty, bounded convergence set. -/
theorem no_holomorphic_extension_at_sSup (hXm : AEMeasurable X μ)
    (hX : ∀ a, 0 ≤ X a) (hne : (integrableExpSet X μ).Nonempty)
    (hbdd : BddAbove (integrableExpSet X μ)) {F : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : DifferentiableOn ℂ F (Metric.ball ((sSup (integrableExpSet X μ) : ℝ) : ℂ) δ))
    (heq : ∀ z ∈ Metric.ball ((sSup (integrableExpSet X μ) : ℝ) : ℂ) δ,
      z.re < sSup (integrableExpSet X μ) → F z = complexMGF X μ z) : False := by
  apply no_holomorphic_extension_at_integrability_boundary hX
    (b := sSup (integrableExpSet X μ)) ?_ ?_ hδ hF heq
  · intro t ht
    by_contra hnot
    have hub : ∀ u ∈ integrableExpSet X μ, u ≤ t := by
      intro u hu
      by_contra hlt
      exact hnot (integrable_exp_of_le hXm hX (lt_of_not_ge hlt).le hu)
    exact (not_le_of_gt ht) (csSup_le hne hub)
  · intro t ht hmem
    exact (not_le_of_gt ht) (le_csSup hbdd hmem)

end LeanEval.NumberTheory.Lagarias.Landau
