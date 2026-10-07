import Playground.Lagarias.LandauContinuation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Positive Mellin integrals and Landau's continuation principle

A nonnegative density on `[a,infinity)`, for `a >= 1`, defines a measure whose
complex moment-generating function is exactly the Mellin power integral.
Both the integral identity and the equivalence of genuine integrability are
proved here. This supplies the bridge needed in one-sided oscillation proofs.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

/-- A globally nonnegative logarithm, agreeing with `log` on the integration ray. -/
noncomputable def positiveLog (x : ℝ) : ℝ := Real.log (max x 1)

lemma positiveLog_nonneg (x : ℝ) : 0 ≤ positiveLog x :=
  Real.log_nonneg (le_max_right x 1)

lemma measurable_positiveLog : Measurable positiveLog :=
  Real.measurable_log.comp (measurable_id.max measurable_const)

lemma positiveLog_eq_log {a x : ℝ} (ha : 1 ≤ a) (hx : a < x) :
    positiveLog x = Real.log x := by
  rw [positiveLog, max_eq_left (ha.trans hx.le)]

/-- The positive density is incorporated into the measure, not assumed in a transform identity. -/
noncomputable def positivePowerMeasure (a : ℝ) (w : ℝ → ℝ≥0) : Measure ℝ :=
  (volume.restrict (Ioi a)).withDensity (fun x => (w x : ℝ≥0∞))

/-- The complex power integral with a nonnegative density. -/
noncomputable def positivePowerIntegral (a : ℝ) (w : ℝ → ℝ≥0) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi a, (w x : ℂ) * (x : ℂ) ^ z

lemma exp_mul_positiveLog_eq_cpow {a x : ℝ} (ha : 1 ≤ a) (hx : a < x) (z : ℂ) :
    Complex.exp (z * (positiveLog x : ℂ)) = (x : ℂ) ^ z := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one (ha.trans hx.le)
  rw [positiveLog_eq_log ha hx, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne'),
    ← Complex.ofReal_log hx0.le, mul_comm]

/-- The exact complex-transform identity, including the change of density. -/
theorem complexMGF_positiveLog_eq_powerIntegral {a : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w) (z : ℂ) :
    complexMGF positiveLog (positivePowerMeasure a w) z = positivePowerIntegral a w z := by
  rw [complexMGF, positivePowerMeasure, integral_withDensity_eq_integral_smul hw]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change w x • Complex.exp (z * (positiveLog x : ℂ)) = (w x : ℂ) * (x : ℂ) ^ z
  rw [exp_mul_positiveLog_eq_cpow ha hx z]
  rfl

/-- Exponential integrability for the density measure is exactly weighted power integrability. -/
theorem mem_integrableExpSet_positiveLog_iff {a : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w) (t : ℝ) :
    t ∈ integrableExpSet positiveLog (positivePowerMeasure a w) ↔
      IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ t) (Ioi a) := by
  change Integrable (fun x => Real.exp (t * positiveLog x)) (positivePowerMeasure a w) ↔ _
  rw [positivePowerMeasure, integrable_withDensity_iff_integrable_smul hw]
  apply integrable_congr
  apply (ae_restrict_iff' measurableSet_Ioi).2
  exact ae_of_all _ fun x hx => by
    change w x • Real.exp (t * positiveLog x) = (w x : ℝ) * x ^ t
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one (ha.trans hx.le)
    rw [positiveLog_eq_log ha hx, Real.rpow_def_of_pos hx0, mul_comm t]
    rfl

/-- Landau's principle directly for positive Mellin power integrals.

The hypotheses include actual convergence in an initial half-plane. A meromorphic
continuation analytic on the real axis cannot have a pole in the larger half-plane.
This theorem does not assume positivity or convergence of an arithmetic error term. -/
theorem no_pole_of_positive_power_integral {a : ℝ} (ha : 1 ≤ a)
    {w : ℝ → ℝ≥0} (hw : Measurable w) {F : ℂ → ℂ} {α β : ℝ}
    (hαβ : α ≤ β)
    (hconv : ∀ t : ℝ, t < α → IntegrableOn (fun x : ℝ => (w x : ℝ) * x ^ t) (Ioi a))
    (hF : MeromorphicOn F {z : ℂ | z.re < β})
    (hreal : ∀ t : ℝ, t < β → AnalyticAt ℂ F (t : ℂ))
    (heq : ∀ z : ℂ, z.re < α → F z = positivePowerIntegral a w z)
    {z : ℂ} (hz : z.re < β) (hpole : meromorphicOrderAt F z < 0) : False := by
  let s : ℝ := α - 1
  have hsα : s < α := by dsimp [s]; linarith
  have hs : s ∈ interior (integrableExpSet positiveLog (positivePowerMeasure a w)) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Iio_mem_nhds hsα)
    intro t ht
    exact (mem_integrableExpSet_positiveLog_iff ha hw t).2 (hconv t ht)
  have heq' : F =ᶠ[𝓝 (s : ℂ)] complexMGF positiveLog (positivePowerMeasure a w) := by
    have hopen : IsOpen {u : ℂ | u.re < α} :=
      isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen.mem_nhds (by simpa using hsα)] with u hu
    exact (heq u hu).trans (complexMGF_positiveLog_eq_powerIntegral ha hw u).symm
  exact no_pole_of_positive_transform_continuation measurable_positiveLog.aemeasurable
    positiveLog_nonneg hs (hsα.trans_le hαβ) hF hreal heq' hz hpole

end LeanEval.NumberTheory.Lagarias.Landau
