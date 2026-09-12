import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
import Playground.Lagarias.LandauPoles

/-!
# Real-axis nonvanishing needed by the Mellin argument

The pinned, source-vendored Abel continuation formula is a proved theorem.
On the real interval `(1/2,1)`, its fractional-part integral is nonnegative
and its elementary term is negative. This proves the real-axis nonvanishing
needed in Lemma 10.2 without importing a prime number theorem or an
oscillation statement.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma zetaAbelFractKernel_ofReal (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    zetaAbelFractKernel (t : ℂ) x = ((Int.fract x * x ^ (-t - 1) : ℝ) : ℂ) := by
  unfold zetaAbelFractKernel
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx]
  push_cast
  rfl

lemma zetaAbelFractIntegral_re_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ (∫ x : ℝ in Ioi 1, zetaAbelFractKernel (t : ℂ) x).re := by
  have hint := ZetaAbelFractKernel.integrableOn_Ioi (t : ℂ) (by simpa using ht)
  change 0 ≤ RCLike.re (∫ x : ℝ in Ioi 1, zetaAbelFractKernel (t : ℂ) x)
  rw [← integral_re hint]
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  have hx0 : 0 ≤ x := le_trans zero_le_one (le_of_lt hx)
  rw [zetaAbelFractKernel_ofReal t hx0]
  change 0 ≤ Int.fract x * x ^ (-t - 1)
  exact mul_nonneg (Int.fract_nonneg x) (Real.rpow_nonneg hx0 _)

/-- The zeta function is strictly negative on the real half-strip. -/
theorem riemannZeta_re_neg_half_to_one {t : ℝ} (ht : 1 / 2 < t) (ht1 : t < 1) :
    (riemannZeta (t : ℂ)).re < 0 := by
  have ht0 : 0 < t := by linarith
  have htne : (t : ℂ) ≠ 1 := by
    intro heq
    have hr : t = (1 : ℝ) := by exact_mod_cast heq
    linarith
  have hformula := riemannZeta_eq_zetaAbelContinuationFormula (t : ℂ)
    (show (t : ℂ) ∈ zetaAbelContinuationDomain from
      ⟨htne, by change (1 / 10 : ℝ) < t; linarith⟩)
  have hdiv : (1 : ℂ) / ((t : ℂ) - 1) = ((1 / (t - 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  unfold zetaAbelContinuationFormula at hformula
  rw [hdiv] at hformula
  have hre := congrArg Complex.re hformula
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  have he : 1 + 1 / (t - 1) = t / (t - 1) := by
    have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht1.ne
    field_simp
    ring
  have hneg : 1 + 1 / (t - 1) < 0 := by
    rw [he]
    exact div_neg_of_pos_of_neg ht0 (by linarith)
  have hnonneg := mul_nonneg ht0.le (zetaAbelFractIntegral_re_nonneg ht0)
  linarith

/-- No real point to the right of `1/2` is a zeta zero. The value at `1`
is Mathlib's nonzero junk value, not a claim of analyticity at the pole. -/
theorem riemannZeta_ne_zero_real_gt_half {t : ℝ} (ht : 1 / 2 < t) :
    riemannZeta (t : ℂ) ≠ 0 := by
  by_cases ht1 : t < 1
  · intro hz
    have hneg := riemannZeta_re_neg_half_to_one ht ht1
    rw [hz, Complex.zero_re] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using le_of_not_gt ht1)

lemma analyticAt_psiErrorContinuation_off_poles {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    AnalyticAt ℂ Landau.psiErrorContinuation s := by
  have hf : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  change AnalyticAt ℂ (fun z : ℂ => -(deriv riemannZeta z) / (z * riemannZeta z) - 1 / (z - 1)) s
  exact (hf.deriv.neg.div (analyticAt_id.mul hf) (mul_ne_zero hs0 hz)).sub
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1))

/-- Away from the removable point `s=0`, the continued prime-error transform
is analytic near every real point used by Landau's principle. -/
theorem analyticAt_shifted_psiErrorContinuation_real {t : ℝ}
    (ht : -(1 / 2) < t) (ht0 : t ≠ 0) :
    AnalyticAt ℂ (fun s : ℂ => Landau.psiErrorContinuation (s + 1)) (t : ℂ) := by
  have ht1 : (1 / 2 : ℝ) < t + 1 := by linarith
  have hz : riemannZeta ((t : ℂ) + 1) ≠ 0 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using riemannZeta_ne_zero_real_gt_half ht1
  have hs0 : (t : ℂ) + 1 ≠ 0 := by
    intro heq
    have hr := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  have hs1 : (t : ℂ) + 1 ≠ 1 := by
    simpa using (show (t : ℂ) ≠ 0 by exact_mod_cast ht0)
  exact (analyticAt_psiErrorContinuation_off_poles hs0 hs1 hz).comp
    (f := fun s : ℂ => s + 1) (by fun_prop)

end LeanEval.NumberTheory.Lagarias.Blueprint
