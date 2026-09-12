import Playground.Lagarias.LandauMGF
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Convex

/-!
# Landau's continuation principle for positive transforms

A meromorphic continuation of a positive transform which is analytic along a
real interval forces convergence throughout that interval. Consequently it
cannot have a pole elsewhere in the corresponding half-plane.

This is the core analytic contradiction in one-sided oscillation arguments.
It is proved for arbitrary measures using the actual transform, rather than
postulating a singularity/convergence correspondence.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- The identity theorem for meromorphic germs on a connected domain. -/
lemma meromorphic_germ_eq_of_preconnected {F G : ℂ → ℂ} {U : Set ℂ} {x y : ℂ}
    (hF : MeromorphicOn F U) (hG : MeromorphicOn G U) (hU : IsPreconnected U)
    (hx : x ∈ U) (hy : y ∈ U) (heq : F =ᶠ[𝓝[≠] x] G) :
    F =ᶠ[𝓝[≠] y] G := by
  have hxorder : meromorphicOrderAt (F - G) x = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp heq)
  have hyorder : meromorphicOrderAt (F - G) y = ⊤ := by
    by_contra hnot
    exact ((hF.sub hG).meromorphicOrderAt_ne_top_of_isPreconnected
      hU hy hx hnot) hxorder
  exact eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp hyorder)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℝ}

lemma mem_integrableExpSet_of_lt_sSup (hXm : AEMeasurable X μ) (hX : ∀ a, 0 ≤ X a)
    (hne : (integrableExpSet X μ).Nonempty) {t : ℝ}
    (ht : t < sSup (integrableExpSet X μ)) : t ∈ integrableExpSet X μ := by
  by_contra hnot
  have hub : ∀ u ∈ integrableExpSet X μ, u ≤ t := by
    intro u hu
    by_contra hlt
    exact hnot (integrable_exp_of_le hXm hX (lt_of_not_ge hlt).le hu)
  exact (not_le_of_gt ht) (csSup_le hne hub)

/-- The interior of the bounded convergence set is exactly the open half-line below its supremum. -/
lemma interior_integrableExpSet_eq_Iio_sSup (hXm : AEMeasurable X μ)
    (hX : ∀ a, 0 ≤ X a) (hne : (integrableExpSet X μ).Nonempty)
    (hbdd : BddAbove (integrableExpSet X μ)) :
    interior (integrableExpSet X μ) = Iio (sSup (integrableExpSet X μ)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨ε, hε, hB⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ht)
    have hpt : t + ε / 2 ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, show t + ε / 2 - t = ε / 2 by ring,
        abs_of_pos (by positivity : 0 < ε / 2)]
      linarith
    have hle := le_csSup hbdd (hB hpt)
    change t < sSup (integrableExpSet X μ)
    linarith
  · intro ht
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Iio_mem_nhds ht)
      (fun u hu => mem_integrableExpSet_of_lt_sSup hXm hX hne hu)

/-- Analytic continuation along the real axis forces genuine exponential integrability. -/
theorem integrableExpSet_of_analytic_real_continuation
    (hXm : AEMeasurable X μ) (hX : ∀ a, 0 ≤ X a) {F : ℂ → ℂ} {β s : ℝ}
    (hs : s ∈ interior (integrableExpSet X μ)) (hsβ : s < β)
    (hF : MeromorphicOn F {z : ℂ | z.re < β})
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
  have hbt : b ≤ t := csSup_le hne hub
  have hbβ : b < β := hbt.trans_lt ht
  have hint := interior_integrableExpSet_eq_Iio_sSup hXm hX hne hbdd
  have hsb : s < b := by simpa only [hint, mem_Iio] using hs
  have hMGF (z : ℂ) (hz : z.re < b) : AnalyticAt ℂ (complexMGF X μ) z := by
    apply analyticAt_complexMGF
    simpa only [hint, mem_Iio] using hz
  have hFb : MeromorphicOn F {z : ℂ | z.re < b} :=
    fun z hz => hF z (hz.trans hbβ)
  have hMGFb : MeromorphicOn (complexMGF X μ) {z : ℂ | z.re < b} :=
    fun z hz => (hMGF z hz).meromorphicAt
  have hgerm (z : ℂ) (hz : z.re < b) : F =ᶠ[𝓝[≠] z] complexMGF X μ :=
    meromorphic_germ_eq_of_preconnected hFb hMGFb (convex_halfSpace_re_lt b).isPreconnected
      (by simpa using hsb) hz (heq.filter_mono nhdsWithin_le_nhds)
  obtain ⟨δ, hδ, hA⟩ := Metric.mem_nhds_iff.mp (hreal b hbβ).eventually_analyticAt
  have hdisc : DifferentiableOn ℂ F (Metric.ball (b : ℂ) δ) :=
    fun z hz => (hA hz).differentiableAt.differentiableWithinAt
  apply no_holomorphic_extension_at_sSup hXm hX hne hbdd hδ hdisc
  intro z hzb hzr
  have hFt : Tendsto F (𝓝[≠] z) (𝓝 (F z)) :=
    (hA hzb).continuousAt.continuousWithinAt.tendsto
  have hGt : Tendsto F (𝓝[≠] z) (𝓝 (complexMGF X μ z)) :=
    (hMGF z hzr).continuousAt.continuousWithinAt.tendsto.congr' (hgerm z hzr).symm
  exact tendsto_nhds_unique hFt hGt

/-- A positive transform analytic along the real axis has no pole in the continued half-plane.
A nonreal pole therefore rules out the proposed one-sided positivity hypothesis. -/
theorem no_pole_of_positive_transform_continuation
    (hXm : AEMeasurable X μ) (hX : ∀ a, 0 ≤ X a) {F : ℂ → ℂ} {β s : ℝ}
    (hs : s ∈ interior (integrableExpSet X μ)) (hsβ : s < β)
    (hF : MeromorphicOn F {z : ℂ | z.re < β})
    (hreal : ∀ t : ℝ, t < β → AnalyticAt ℂ F (t : ℂ))
    (heq : F =ᶠ[𝓝 (s : ℂ)] complexMGF X μ) {z : ℂ}
    (hz : z.re < β) (hpole : meromorphicOrderAt F z < 0) : False := by
  have hconv := integrableExpSet_of_analytic_real_continuation hXm hX hs hsβ hF hreal heq
  have hMGF (w : ℂ) (hw : w.re < β) : AnalyticAt ℂ (complexMGF X μ) w := by
    apply analyticAt_complexMGF
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Iio_mem_nhds hw) (fun u hu => hconv u hu)
  have hMGFon : MeromorphicOn (complexMGF X μ) {w : ℂ | w.re < β} :=
    fun w hw => (hMGF w hw).meromorphicAt
  have hgerm := meromorphic_germ_eq_of_preconnected hF hMGFon
    (convex_halfSpace_re_lt β).isPreconnected (by simpa using hsβ) hz
    (heq.filter_mono nhdsWithin_le_nhds)
  have horder := meromorphicOrderAt_congr hgerm
  rw [horder] at hpole
  exact (not_lt_of_ge (hMGF z hz).meromorphicOrderAt_nonneg) hpole

end LeanEval.NumberTheory.Lagarias.Landau
