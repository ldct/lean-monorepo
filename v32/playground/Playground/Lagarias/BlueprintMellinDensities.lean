import Playground.Lagarias.BlueprintMellinOperations
import Playground.Lagarias.BlueprintJIntegral

/-!
# The actual densities in the two prime-error Mellin transforms

Blueprint: (10.2), (10.5), and the integral side of (10.6).
The functions below use the actual `R=psi-id` and `J`. Their convergence and
logarithmic derivatives are consequences of proved bounds. In particular,
the relation between the second derivative of the smoothed integral and
`Q-Q'` is proved, not supplied as a hypothesis.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

noncomputable def primeErrorDensity (x : ℝ) : ℂ := (R x / x : ℝ)
noncomputable def smoothingDensity (x : ℝ) : ℂ := (R x * x * w x : ℝ)

noncomputable def Jhat (a : ℝ) : ℂ → ℂ := truncatedMellin a (fun x => (J x : ℂ))
noncomputable def QIntegral (a : ℝ) : ℂ → ℂ := truncatedMellin a primeErrorDensity
noncomputable def WIntegral (a : ℝ) : ℂ → ℂ := truncatedMellin a smoothingDensity

@[fun_prop] lemma measurable_primeErrorDensity : Measurable primeErrorDensity := by
  unfold primeErrorDensity
  fun_prop

@[fun_prop] lemma measurable_smoothingDensity : Measurable smoothingDensity := by
  unfold smoothingDensity w
  fun_prop

lemma primeErrorDensity_bound {x : ℝ} (hx : 0 < x) : ‖primeErrorDensity x‖ ≤ 8 := by
  rw [primeErrorDensity, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hx]
  exact (div_le_iff₀ hx).mpr (abs_R_le_eight_mul hx.le)

noncomputable def smoothingDensityBound : ℝ :=
  8 * (1 / Real.log 2 + 1 / (Real.log 2) ^ 2)

lemma smoothingDensityBound_nonneg : 0 ≤ smoothingDensityBound := by
  unfold smoothingDensityBound
  positivity

lemma smoothingDensity_bound {x : ℝ} (hx : 2 ≤ x) :
    ‖smoothingDensity x‖ ≤ smoothingDensityBound := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlle : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hw0 : 0 ≤ w x := (w_pos (by linarith : 1 < x)).le
  have hfactor : x * x * w x = 1 / Real.log x + 1 / (Real.log x) ^ 2 := by
    unfold w
    field_simp
  rw [smoothingDensity, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos hx0, abs_of_nonneg hw0]
  calc
    |R x| * x * w x ≤ (8 * x) * x * w x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_R_le_eight_mul hx0.le) hx0.le) hw0
    _ = 8 * (1 / Real.log x + 1 / (Real.log x) ^ 2) := by
      rw [← hfactor]
      ring
    _ ≤ smoothingDensityBound := by
      unfold smoothingDensityBound
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact div_le_div_of_nonneg_left zero_le_one hl2 hlle
      · exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hl2)
          (pow_le_pow_left₀ hl2.le hlle 2)

lemma primeErrorDensity_polynomial_bound {a : ℝ} (ha : 1 ≤ a) :
    ∀ x : ℝ, a < x → ‖primeErrorDensity x‖ ≤ 8 * x ^ (0 : ℝ) := by
  intro x hx
  simpa only [Real.rpow_zero, mul_one] using
    primeErrorDensity_bound (zero_lt_one.trans_le (ha.trans hx.le))

lemma smoothingDensity_polynomial_bound {a : ℝ} (ha : 2 ≤ a) :
    ∀ x : ℝ, a < x → ‖smoothingDensity x‖ ≤ smoothingDensityBound * x ^ (0 : ℝ) := by
  intro x hx
  simpa only [Real.rpow_zero, mul_one] using smoothingDensity_bound (ha.trans hx.le)

lemma J_polynomial_bound {a : ℝ} (ha : 2 ≤ a) :
    ∀ x : ℝ, a < x → ‖(J x : ℂ)‖ ≤ (22 / Real.log 2) * x ^ (0 : ℝ) := by
  intro x hx
  simpa only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_zero, mul_one] using
    abs_J_le_uniform (ha.trans hx.le)

lemma integrableOn_QIntegral {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => primeErrorDensity x * (x : ℂ) ^ (-s - 1)) (Ioi a) :=
  integrableOn_truncatedMellin ha (by norm_num) measurable_primeErrorDensity
    (primeErrorDensity_polynomial_bound ha) hs

lemma integrableOn_WIntegral {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => smoothingDensity x * (x : ℂ) ^ (-s - 1)) (Ioi a) :=
  integrableOn_truncatedMellin (by linarith : 1 ≤ a) smoothingDensityBound_nonneg
    measurable_smoothingDensity (smoothingDensity_polynomial_bound ha) hs

lemma integrableOn_Jhat {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (J x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi a) :=
  integrableOn_truncatedMellin (by linarith : 1 ≤ a) (by positivity)
    (Complex.measurable_ofReal.comp measurable_J) (J_polynomial_bound ha) hs

lemma analyticAt_QIntegral {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (QIntegral a) s :=
  analyticAt_truncatedMellin ha (by norm_num) measurable_primeErrorDensity
    (primeErrorDensity_polynomial_bound ha) hs

lemma analyticAt_WIntegral {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (WIntegral a) s :=
  analyticAt_truncatedMellin (by linarith : 1 ≤ a) smoothingDensityBound_nonneg
    measurable_smoothingDensity (smoothingDensity_polynomial_bound ha) hs

lemma analyticAt_Jhat {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (Jhat a) s :=
  analyticAt_truncatedMellin (by linarith : 1 ≤ a) (by positivity)
    (Complex.measurable_ofReal.comp measurable_J) (J_polynomial_bound ha) hs

lemma double_logWeight_smoothingDensity {x : ℝ} (hx : 1 < x) :
    logWeight (logWeight smoothingDensity) x = primeErrorDensity x + logWeight primeErrorDensity x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hx).ne'
  have hl0 : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hx).ne'
  unfold logWeight smoothingDensity primeErrorDensity w
  push_cast
  field_simp
  ring

/-- Two logarithmic derivatives give exactly Q-Q', for the defining integrals. -/
theorem deriv_deriv_WIntegral {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    deriv (deriv (WIntegral a)) s = QIntegral a s - deriv (QIntegral a) s := by
  have ha1 : 1 ≤ a := by linarith
  have hW := (hasDerivAt_deriv_truncatedMellin ha1 smoothingDensityBound_nonneg
    measurable_smoothingDensity (smoothingDensity_polynomial_bound ha) hs).deriv
  have hQ := (hasDerivAt_truncatedMellin ha1 (by norm_num) measurable_primeErrorDensity
    (primeErrorDensity_polynomial_bound ha1) hs).deriv
  have hlogInt : IntegrableOn (fun x : ℝ => logWeight primeErrorDensity x *
      (x : ℂ) ^ (-s - 1)) (Ioi a) := by
    have hε : 0 < s.re / 2 := half_pos hs
    apply integrableOn_truncatedMellin ha1 (div_nonneg (by norm_num) hε.le)
      (measurable_logWeight measurable_primeErrorDensity)
      (logWeight_bound ha1 (by norm_num) hε (primeErrorDensity_polynomial_bound ha1))
    linarith
  change deriv (deriv (truncatedMellin a smoothingDensity)) s =
    truncatedMellin a primeErrorDensity s - deriv (truncatedMellin a primeErrorDensity) s
  rw [hW, hQ, sub_neg_eq_add]
  calc
    _ = truncatedMellin a (fun x => primeErrorDensity x + logWeight primeErrorDensity x) s := by
      apply truncatedMellin_congr (by linarith : 0 ≤ a)
      intro x hx
      exact double_logWeight_smoothingDensity (by linarith [show a < x from hx])
    _ = _ := truncatedMellin_add (by linarith : 0 ≤ a) (integrableOn_QIntegral ha1 hs) hlogInt

end LeanEval.NumberTheory.Lagarias.Blueprint
