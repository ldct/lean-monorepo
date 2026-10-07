import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Analytic primitives along a real interval

Blueprint: Lemma 10.3. A horizontal real segment followed by a vertical
segment gives a concrete primitive near every real point of an interval.
Only analyticity near that real interval is required: off-axis singularities
and the logarithmic monodromy of primitives are not assumed away.
Two primitives can be normalized to match a given analytic function and its
first derivative at the base point, and then agree with its germ whenever
the second derivatives agree.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set Metric
open scoped Topology

noncomputable def axisPrimitive (c : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.wedgeIntegral (c : ℂ) z F

lemma axisPrimitive_real (c t : ℝ) (F : ℂ → ℂ) :
    axisPrimitive c F (t : ℂ) = ∫ x : ℝ in c..t, F (x : ℂ) := by
  simp [axisPrimitive, Complex.wedgeIntegral]

@[simp] lemma axisPrimitive_self (c : ℝ) (F : ℂ → ℂ) : axisPrimitive c F (c : ℂ) = 0 := by
  rw [axisPrimitive_real, intervalIntegral.integral_same]

lemma intervalIntegrable_real_of_axis_analytic {β a b : ℝ} {F : ℂ → ℂ}
    (hF : ∀ t : ℝ, β < t → AnalyticAt ℂ F (t : ℂ)) (ha : β < a) (hb : β < b) :
    IntervalIntegrable (fun x : ℝ => F (x : ℂ)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hβ : β < x := (lt_min ha hb).trans_le hx.1
  exact ((hF x hβ).continuousAt.comp x Complex.continuous_ofReal.continuousAt).continuousWithinAt

lemma axisPrimitive_recenter {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ))
    (hc : β < c) (ht : β < t) {z : ℂ} (hz : β < z.re) :
    axisPrimitive c F z = axisPrimitive c F (t : ℂ) + Complex.wedgeIntegral (t : ℂ) z F := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_real_of_axis_analytic hF hc ht)
    (intervalIntegrable_real_of_axis_analytic hF ht hz)
  simp only [axisPrimitive, Complex.wedgeIntegral, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, intervalIntegral.integral_same, smul_zero, add_zero]
  rw [← hadd]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- The derivative identity holds on a complex neighborhood, not just at a real point. -/
lemma eventually_hasDerivAt_axisPrimitive {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (ht : β < t) :
    ∀ᶠ z : ℂ in 𝓝 (t : ℂ), HasDerivAt (axisPrimitive c F) (F z) z := by
  have hhood : ∀ᶠ z : ℂ in 𝓝 (t : ℂ), AnalyticAt ℂ F z ∧ β < z.re := by
    filter_upwards [(hF t ht).eventually_analyticAt,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using ht)] with z hz hz'
    exact ⟨hz, hz'⟩
  obtain ⟨δ, hδ, hA⟩ := Metric.mem_nhds_iff.mp hhood
  have hd : DifferentiableOn ℂ F (ball (t : ℂ) δ) :=
    fun z hz => (hA hz).1.differentiableAt.differentiableWithinAt
  filter_upwards [Metric.ball_mem_nhds (t : ℂ) hδ] with z hz
  have hw := hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hz
  apply (hw.const_add (axisPrimitive c F (t : ℂ))).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact axisPrimitive_recenter hF hc ht (hA hu).2

lemma hasDerivAt_axisPrimitive_real {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (ht : β < t) :
    HasDerivAt (axisPrimitive c F) (F (t : ℂ)) (t : ℂ) :=
  (eventually_hasDerivAt_axisPrimitive hF hc ht).self_of_nhds

lemma analyticAt_axisPrimitive_real {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (ht : β < t) :
    AnalyticAt ℂ (axisPrimitive c F) (t : ℂ) := by
  obtain ⟨δ, hδ, hD⟩ := Metric.mem_nhds_iff.mp (eventually_hasDerivAt_axisPrimitive hF hc ht)
  have hd : DifferentiableOn ℂ (axisPrimitive c F) (ball (t : ℂ) δ) :=
    fun z hz => (hD hz).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (Metric.ball_mem_nhds (t : ℂ) hδ)

lemma deriv_axisPrimitive_germ {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (ht : β < t) :
    deriv (axisPrimitive c F) =ᶠ[𝓝 (t : ℂ)] F :=
  (eventually_hasDerivAt_axisPrimitive hF hc ht).mono (fun z hz => hz.deriv)

/-- Two analytic germs with equal second derivatives and equal first jets coincide. -/
lemma analytic_germ_eq_of_second_deriv_eq {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c)
    (h2 : deriv (deriv f) =ᶠ[𝓝 c] deriv (deriv g))
    (h0 : f c = g c) (h1 : deriv f c = deriv g c) : f =ᶠ[𝓝 c] g := by
  have hhood : ∀ᶠ z : ℂ in 𝓝 c,
      AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z ∧ deriv (deriv f) z = deriv (deriv g) z := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, h2] with z hz hz' hz2
    exact ⟨hz, hz', hz2⟩
  obtain ⟨δ, hδ, hA⟩ := Metric.mem_nhds_iff.mp hhood
  have hc : c ∈ ball c δ := mem_ball_self hδ
  have hpre : IsPreconnected (ball c δ) := (convex_ball c δ).isPreconnected
  have hdf : DifferentiableOn ℂ (deriv f) (ball c δ) :=
    fun z hz => (hA hz).1.deriv.differentiableAt.differentiableWithinAt
  have hdg : DifferentiableOn ℂ (deriv g) (ball c δ) :=
    fun z hz => (hA hz).2.1.deriv.differentiableAt.differentiableWithinAt
  have hdEq : EqOn (deriv f) (deriv g) (ball c δ) :=
    isOpen_ball.eqOn_of_deriv_eq hpre hdf hdg (fun z hz => (hA hz).2.2) hc h1
  have hf' : DifferentiableOn ℂ f (ball c δ) :=
    fun z hz => (hA hz).1.differentiableAt.differentiableWithinAt
  have hg' : DifferentiableOn ℂ g (ball c δ) :=
    fun z hz => (hA hz).2.1.differentiableAt.differentiableWithinAt
  have hEq := isOpen_ball.eqOn_of_deriv_eq hpre hf' hg' hdEq hc h0
  filter_upwards [Metric.ball_mem_nhds c hδ] with z hz
  exact hEq hz

noncomputable def normalizedSecondPrimitive (c : ℝ) (F : ℂ → ℂ) (v0 v1 : ℂ) (z : ℂ) : ℂ :=
  axisPrimitive c (axisPrimitive c F) z + v0 + (z - c) * v1

@[simp] lemma normalizedSecondPrimitive_self (c : ℝ) (F : ℂ → ℂ) (v0 v1 : ℂ) :
    normalizedSecondPrimitive c F v0 v1 (c : ℂ) = v0 := by
  simp [normalizedSecondPrimitive]

lemma analyticAt_normalizedSecondPrimitive_real {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (ht : β < t)
    (v0 v1 : ℂ) : AnalyticAt ℂ (normalizedSecondPrimitive c F v0 v1) (t : ℂ) := by
  have hA : ∀ u : ℝ, β < u → AnalyticAt ℂ (axisPrimitive c F) (u : ℂ) :=
    fun u hu => analyticAt_axisPrimitive_real hF hc hu
  exact ((analyticAt_axisPrimitive_real hA hc ht).add analyticAt_const).add
    ((analyticAt_id.sub analyticAt_const).mul analyticAt_const)

set_option backward.isDefEq.respectTransparency false in
lemma deriv_normalizedSecondPrimitive_germ {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (ht : β < t)
    (v0 v1 : ℂ) :
    deriv (normalizedSecondPrimitive c F v0 v1) =ᶠ[𝓝 (t : ℂ)] (fun z => axisPrimitive c F z + v1) := by
  have hA : ∀ u : ℝ, β < u → AnalyticAt ℂ (axisPrimitive c F) (u : ℂ) :=
    fun u hu => analyticAt_axisPrimitive_real hF hc hu
  filter_upwards [eventually_hasDerivAt_axisPrimitive hA hc ht] with z hz
  have hlin : HasDerivAt (fun u : ℂ => (u - c) * v1) v1 z := by
    convert! ((hasDerivAt_id z).sub_const (c : ℂ)).mul_const v1 using 1 <;> simp
  have hn : HasDerivAt (normalizedSecondPrimitive c F v0 v1) (axisPrimitive c F z + v1) z := by
    convert! (hz.add_const v0).add hlin using 1
  exact hn.deriv

lemma deriv_normalizedSecondPrimitive_self {β c : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (v0 v1 : ℂ) :
    deriv (normalizedSecondPrimitive c F v0 v1) (c : ℂ) = v1 := by
  simpa only [axisPrimitive_self, zero_add] using
    (deriv_normalizedSecondPrimitive_germ hF hc hc v0 v1).self_of_nhds

lemma second_deriv_normalizedSecondPrimitive_germ {β c t : ℝ} {F : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c) (ht : β < t)
    (v0 v1 : ℂ) : deriv (deriv (normalizedSecondPrimitive c F v0 v1)) =ᶠ[𝓝 (t : ℂ)] F := by
  have hh := (deriv_normalizedSecondPrimitive_germ hF hc ht v0 v1).deriv
  filter_upwards [hh, deriv_axisPrimitive_germ hF hc ht] with z hz hz'
  rw [hz, deriv_add_const, hz']

/-- The normalized construction continues the original analytic germ. -/
theorem normalizedSecondPrimitive_germ_eq {β c : ℝ} {F W : ℂ → ℂ}
    (hF : ∀ u : ℝ, β < u → AnalyticAt ℂ F (u : ℂ)) (hc : β < c)
    (hW : AnalyticAt ℂ W (c : ℂ)) (h2 : deriv (deriv W) =ᶠ[𝓝 (c : ℂ)] F) :
    normalizedSecondPrimitive c F (W c) (deriv W c) =ᶠ[𝓝 (c : ℂ)] W := by
  apply analytic_germ_eq_of_second_deriv_eq
    (analyticAt_normalizedSecondPrimitive_real hF hc hc _ _) hW
    ((second_deriv_normalizedSecondPrimitive_germ hF hc hc _ _).trans h2.symm)
  · exact normalizedSecondPrimitive_self c F _ _
  · exact deriv_normalizedSecondPrimitive_self hF hc _ _

end LeanEval.NumberTheory.Lagarias.Blueprint
