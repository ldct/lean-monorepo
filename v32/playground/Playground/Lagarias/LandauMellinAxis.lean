import Playground.Lagarias.LandauRealAxis

/-!
# Positive Mellin transforms in the blueprint convention

The manuscript uses `integral f(x) x^(-s-1)`, not the power-integral parameter
used in the underlying moment-generating-function API. The affine involution
`s |-> -s-1` reverses the convergence half-plane. This file performs that
translation and proves analyticity of the actual integral once convergence is
known, rather than assuming a continuation already exists on that half-plane.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

noncomputable def positiveMellin (a : ℝ) (w : ℝ → ℝ≥0) (s : ℂ) : ℂ :=
  positivePowerIntegral a w (-s - 1)

lemma positiveMellin_eq_integral (a : ℝ) (w : ℝ → ℝ≥0) (s : ℂ) :
    positiveMellin a w s =
      ∫ x : ℝ in Ioi a, (w x : ℂ) * (x : ℂ) ^ (-s - 1) := rfl

lemma analyticAt_positivePowerIntegral_of_convergence {a β : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w)
    (hconv : ∀ t : ℝ, t < β → IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ t) (Ioi a))
    {z : ℂ} (hz : z.re < β) : AnalyticAt ℂ (positivePowerIntegral a w) z := by
  have hint : z.re ∈ interior (integrableExpSet positiveLog (positivePowerMeasure a w)) := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (Iio_mem_nhds hz)
      (fun t ht => (mem_integrableExpSet_positiveLog_iff ha hw t).mpr (hconv t ht))
  have heq : positivePowerIntegral a w = complexMGF positiveLog (positivePowerMeasure a w) :=
    funext fun u => (complexMGF_positiveLog_eq_powerIntegral ha hw u).symm
  rw [heq]
  exact analyticAt_complexMGF hint

/-- Absolute real convergence implies analyticity of the actual Mellin integral. -/
theorem analyticAt_positiveMellin_of_convergence {a β : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w)
    (hconv : ∀ t : ℝ, β < t →
      IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ (-t - 1)) (Ioi a))
    {s : ℂ} (hs : β < s.re) : AnalyticAt ℂ (positiveMellin a w) s := by
  have hpower : ∀ t : ℝ, t < -β - 1 →
      IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ t) (Ioi a) := by
    intro t ht
    have hc := hconv (-t - 1) (by linarith)
    simpa only [show -(-t - 1) - 1 = t by ring] using hc
  have harg : (-s - 1).re < -β - 1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  exact (analyticAt_positivePowerIntegral_of_convergence ha hw hpower harg).comp
    (f := fun z : ℂ => -z - 1) (x := s)
    (show AnalyticAt ℂ (fun z : ℂ => -z - 1) s by fun_prop)

/-- Landau's principle upgrades real-axis continuation to genuine convergence
throughout the continued half-plane. This is the step used in Proposition 10.4. -/
theorem mellin_integrable_of_real_axis_germs {a : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w) {F : ℂ → ℂ} {c β : ℝ}
    (hconv : ∀ t : ℝ, c < t →
      IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ (-t - 1)) (Ioi a))
    (hreal : ∀ t : ℝ, β < t → AnalyticAt ℂ F (t : ℂ))
    (heq : ∀ z : ℂ, c < z.re → F z = positiveMellin a w z) :
    ∀ t : ℝ, β < t → IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ (-t - 1)) (Ioi a) := by
  let G : ℂ → ℂ := fun z => F (-z - 1)
  have hpower : ∀ t : ℝ, t < -c - 1 →
      IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ t) (Ioi a) := by
    intro t ht
    have hc := hconv (-t - 1) (by linarith)
    simpa only [show -(-t - 1) - 1 = t by ring] using hc
  have hGreal : ∀ t : ℝ, t < -β - 1 → AnalyticAt ℂ G (t : ℂ) := by
    intro t ht
    have hF := hreal (-t - 1) (by linarith)
    have harg : ((-t - 1 : ℝ) : ℂ) = -(t : ℂ) - 1 := by push_cast; rfl
    rw [harg] at hF
    exact hF.comp (f := fun z : ℂ => -z - 1) (x := (t : ℂ))
      (show AnalyticAt ℂ (fun z : ℂ => -z - 1) (t : ℂ) by fun_prop)
  have hGeq : ∀ z : ℂ, z.re < -c - 1 → G z = positivePowerIntegral a w z := by
    intro z hz
    have hz' : c < (-z - 1).re := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    have hF := heq (-z - 1) hz'
    simpa only [G, positiveMellin, show -(-z - 1) - 1 = z by ring] using hF
  intro t ht
  exact power_integrable_of_real_axis_germs ha hw hpower hGreal hGeq
    (-t - 1) (by linarith)

/-- The holomorphic function obtained after Landau is the defining integral,
not an assumed meromorphic extension. -/
theorem analyticAt_positiveMellin_of_real_axis_germs {a : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w) {F : ℂ → ℂ} {c β : ℝ}
    (hconv : ∀ t : ℝ, c < t →
      IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ (-t - 1)) (Ioi a))
    (hreal : ∀ t : ℝ, β < t → AnalyticAt ℂ F (t : ℂ))
    (heq : ∀ z : ℂ, c < z.re → F z = positiveMellin a w z)
    {s : ℂ} (hs : β < s.re) : AnalyticAt ℂ (positiveMellin a w) s :=
  analyticAt_positiveMellin_of_convergence ha hw
    (mellin_integrable_of_real_axis_germs ha hw hconv hreal heq) hs

end LeanEval.NumberTheory.Lagarias.Landau
