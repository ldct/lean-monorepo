import Playground.Lagarias.LandauMellin

/-!
# Landau continuation along the real axis only

Blueprint: the supplied self-contained manuscript, Lemmas 10.1 and 10.3 and
Proposition 10.4. The old continuation theorem requires a globally meromorphic
continuation. That is unnecessarily strong for the smoothed error: taking
primitives can produce logarithmic singularities away from the real axis.

Here a single function analytic near each real point, and agreeing with the
original transform at one interior point, suffices. No off-axis meromorphic
continuation, simply connected tube, or zero-free half-plane is assumed.
The identity theorem propagates germs along the connected real interval.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℝ}

/-- Real-axis analytic continuation of a positive transform forces convergence.
The continuation need not be meromorphic away from the real axis. -/
theorem integrableExpSet_of_real_axis_germs
    (hXm : AEMeasurable X μ) (hX : ∀ a, 0 ≤ X a) {F : ℂ → ℂ} {β s : ℝ}
    (hs : s ∈ interior (integrableExpSet X μ))
    (hreal : ∀ t : ℝ, t < β → AnalyticAt ℂ F (t : ℂ))
    (heq : F =ᶠ[𝓝 (s : ℂ)] complexMGF X μ) :
    ∀ t : ℝ, t < β → t ∈ integrableExpSet X μ := by
  intro t ht
  by_contra hnot
  have hne : (integrableExpSet X μ).Nonempty := ⟨s, interior_subset hs⟩
  have hub : ∀ u ∈ integrableExpSet X μ, u ≤ t := by
    intro u hu
    by_contra hlt
    exact hnot (integrable_exp_of_le hXm hX (lt_of_not_ge hlt).le hu)
  have hbdd : BddAbove (integrableExpSet X μ) := ⟨t, hub⟩
  let b := sSup (integrableExpSet X μ)
  have hbβ : b < β := (csSup_le hne hub).trans_lt ht
  have hint := interior_integrableExpSet_eq_Iio_sSup hXm hX hne hbdd
  have hsb : s < b := by simpa only [hint, mem_Iio] using hs
  have hMGF (z : ℂ) (hz : z.re < b) : AnalyticAt ℂ (complexMGF X μ) z := by
    apply analyticAt_complexMGF
    simpa only [hint, mem_Iio] using hz
  let axis : Set ℂ := Complex.ofReal '' Iio b
  have haxis : IsPreconnected axis :=
    isPreconnected_Iio.image Complex.ofReal Complex.continuous_ofReal.continuousOn
  have hFaxis : MeromorphicOn F axis := by
    rintro z ⟨u, hu, rfl⟩
    exact (hreal u (hu.trans hbβ)).meromorphicAt
  have hGaxis : MeromorphicOn (complexMGF X μ) axis := by
    rintro z ⟨u, hu, rfl⟩
    exact (hMGF (u : ℂ) (by simpa using hu)).meromorphicAt
  have hgerm (u : ℝ) (hu : u < b) : F =ᶠ[𝓝 (u : ℂ)] complexMGF X μ := by
    apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hreal u (hu.trans hbβ)).continuousAt (hMGF (u : ℂ) (by simpa using hu)).continuousAt).mpr
    exact meromorphic_germ_eq_of_preconnected hFaxis hGaxis haxis
      ⟨s, hsb, rfl⟩ ⟨u, hu, rfl⟩ (heq.filter_mono nhdsWithin_le_nhds)
  obtain ⟨δ, hδ, hA⟩ := Metric.mem_nhds_iff.mp (hreal b hbβ).eventually_analyticAt
  have hdisc : DifferentiableOn ℂ F (Metric.ball (b : ℂ) δ) :=
    fun z hz => (hA hz).differentiableAt.differentiableWithinAt
  let u : ℝ := b - δ / 2
  have hub' : u < b := by dsimp [u]; linarith
  have huBall : (u : ℂ) ∈ Metric.ball (b : ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show u - b = -(δ / 2) by dsimp [u]; ring,
      abs_neg, abs_of_pos (by positivity : 0 < δ / 2)]
    linarith
  let V : Set ℂ := Metric.ball (b : ℂ) δ ∩ {z : ℂ | z.re < b}
  have hFV : AnalyticOnNhd ℂ F V := fun z hz => hA hz.1
  have hGV : AnalyticOnNhd ℂ (complexMGF X μ) V := fun z hz => hMGF z hz.2
  have hV : IsPreconnected V :=
    ((convex_ball (b : ℂ) δ).inter (convex_halfSpace_re_lt b)).isPreconnected
  have huV : (u : ℂ) ∈ V := ⟨huBall, by simpa using hub'⟩
  have heqV : EqOn F (complexMGF X μ) V :=
    hFV.eqOn_of_preconnected_of_eventuallyEq hGV hV huV (hgerm u hub')
  apply no_holomorphic_extension_at_sSup hXm hX hne hbdd hδ hdisc
  intro z hz hzb
  exact heqV ⟨hz, hzb⟩

/-- Positivity upgrades continuation along the real axis to actual analyticity
on the entire half-plane of convergence. -/
theorem analyticAt_complexMGF_of_real_axis_germs
    (hXm : AEMeasurable X μ) (hX : ∀ a, 0 ≤ X a) {F : ℂ → ℂ} {β s : ℝ}
    (hs : s ∈ interior (integrableExpSet X μ))
    (hreal : ∀ t : ℝ, t < β → AnalyticAt ℂ F (t : ℂ))
    (heq : F =ᶠ[𝓝 (s : ℂ)] complexMGF X μ) {z : ℂ} (hz : z.re < β) :
    AnalyticAt ℂ (complexMGF X μ) z := by
  apply analyticAt_complexMGF
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (Iio_mem_nhds hz)
    (fun t ht => integrableExpSet_of_real_axis_germs hXm hX hs hreal heq t ht)

/-- The same result for positive power integrals, with no global meromorphicity
hypothesis on their continuation. -/
theorem power_integrable_of_real_axis_germs {a : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w) {F : ℂ → ℂ} {c β : ℝ}
    (hconv : ∀ t : ℝ, t < c → IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ t) (Ioi a))
    (hreal : ∀ t : ℝ, t < β → AnalyticAt ℂ F (t : ℂ))
    (heq : ∀ z : ℂ, z.re < c → F z = positivePowerIntegral a w z) :
    ∀ t : ℝ, t < β → IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ t) (Ioi a) := by
  let s : ℝ := c - 1
  have hsc : s < c := by dsimp [s]; linarith
  have hs : s ∈ interior (integrableExpSet positiveLog (positivePowerMeasure a w)) := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Iio_mem_nhds hsc)
      (fun t ht => (mem_integrableExpSet_positiveLog_iff ha hw t).mpr (hconv t ht))
  have hgerm : F =ᶠ[𝓝 (s : ℂ)] complexMGF positiveLog (positivePowerMeasure a w) := by
    have hopen : IsOpen {z : ℂ | z.re < c} := isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen.mem_nhds (by simpa using hsc)] with z hz
    exact (heq z hz).trans (complexMGF_positiveLog_eq_powerIntegral ha hw z).symm
  intro t ht
  exact (mem_integrableExpSet_positiveLog_iff ha hw t).mp
    (integrableExpSet_of_real_axis_germs measurable_positiveLog.aemeasurable
      positiveLog_nonneg hs hreal hgerm t ht)

end LeanEval.NumberTheory.Lagarias.Landau
