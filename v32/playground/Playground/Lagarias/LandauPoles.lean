import Playground.Lagarias.LandauZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Convex

/-!
# Genuine poles of the Chebyshev-error transform

A zeta zero produces a simple pole of the logarithmic derivative, regardless
of its multiplicity. Multiplication by `-1/s` and addition of `-1/(s-1)` do
not remove that pole away from 0 and 1. We establish this using meromorphic
orders, so Lean's totalized values at division by zero play no role.

These are analytic prerequisites. They do not yet prove the oscillation of
Robin's divisor-sum error or the final Lagarias equivalence.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open Filter Set
open scoped Topology

/-- A logarithmic derivative has a simple pole at a finite nonzero meromorphic order. -/
lemma order_logDeriv_eq_neg_one {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z)
    (hzero : meromorphicOrderAt f z ≠ 0) (hfinite : meromorphicOrderAt f z ≠ ⊤) :
    meromorphicOrderAt (logDeriv f) z = ((-1 : ℤ) : WithTop ℤ) := by
  lift meromorphicOrderAt f z to ℤ using hfinite with n hn
  have hn0 : n ≠ 0 := by exact_mod_cast hzero
  have hderiv := meromorphicOrderAt_deriv_eq_sub_one
    (Int.cast_ne_zero.mpr hn0 : (n : ℂ) ≠ 0) hn.symm
  change meromorphicOrderAt (deriv f / f) z = _
  rw [meromorphicOrderAt_div hf.deriv hf, hderiv, ← hn]
  norm_cast
  ring

/-- A nonvanishing analytic factor and an analytic summand cannot cancel that pole. -/
lemma order_weighted_logDeriv_add {f a b : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (hzero : meromorphicOrderAt f z ≠ 0)
    (hfinite : meromorphicOrderAt f z ≠ ⊤)
    (ha : AnalyticAt ℂ a z) (ha0 : a z ≠ 0) (hb : AnalyticAt ℂ b z) :
    meromorphicOrderAt (a * logDeriv f + b) z = ((-1 : ℤ) : WithTop ℤ) := by
  have hlog := order_logDeriv_eq_neg_one hf hzero hfinite
  have hp : meromorphicOrderAt (a * logDeriv f) z = ((-1 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_mul_of_ne_zero ha ha0).trans hlog
  have hlt : meromorphicOrderAt (a * logDeriv f) z < meromorphicOrderAt b z := by
    rw [hp]
    have hneg : ((-1 : ℤ) : WithTop ℤ) < 0 := by exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)
    exact lt_of_lt_of_le hneg hb.meromorphicOrderAt_nonneg
  exact (meromorphicOrderAt_add_eq_left_of_lt hb.meromorphicAt hlt).trans hp

/-- Zeta has finite order everywhere strictly to the left of its pole at 1.
The identity theorem is applied in the connected left half-plane, using `zeta(0) != 0`. -/
lemma zeta_order_ne_top_of_re_lt_one {z : ℂ} (hz : z.re < 1) :
    meromorphicOrderAt riemannZeta z ≠ ⊤ := by
  have hU : MeromorphicOn riemannZeta {w : ℂ | w.re < 1} := by
    intro w hw
    have hw1 : w ≠ 1 := by
      intro h
      subst w
      change (1 : ℝ) < 1 at hw
      exact lt_irrefl _ hw
    exact (analyticOn_riemannZeta w hw1).meromorphicAt
  have ha0 : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 (by simp)
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have horder0 : meromorphicOrderAt riemannZeta 0 = 0 := by
    simp [ha0.meromorphicOrderAt_eq, ha0.analyticOrderAt_eq_zero.mpr hζ0]
  exact hU.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_halfSpace_re_lt 1).isPreconnected
    (x := 0) (by simp) hz (by rw [horder0]; simp)

/-- At a zeta zero away from 1 the meromorphic order is nonzero. -/
lemma zeta_order_ne_zero_of_zero {z : ℂ} (hz : z ≠ 1) (hζ : riemannZeta z = 0) :
    meromorphicOrderAt riemannZeta z ≠ 0 := by
  have ha : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz
  have hn : analyticOrderAt riemannZeta z ≠ 0 := by
    intro h
    exact (ha.analyticOrderAt_eq_zero.mp h) hζ
  rw [ha.meromorphicOrderAt_eq]
  cases h : analyticOrderAt riemannZeta z with
  | top => simp
  | coe n =>
      have hn0 : n ≠ 0 := by
        intro hn0
        apply hn
        simpa [hn0] using h
      simpa using hn0

/-- The expression obtained by continuing the actual error transform from `re s > 1`. -/
noncomputable def psiErrorContinuation (s : ℂ) : ℂ :=
  -deriv riemannZeta s / (s * riemannZeta s) - 1 / (s - 1)

lemma psiErrorContinuation_eq_weighted_logDeriv :
    psiErrorContinuation =
      (fun s : ℂ => -1 / s) * logDeriv riemannZeta + (fun s : ℂ => -1 / (s - 1)) := by
  funext s
  simp only [psiErrorContinuation, logDeriv, Pi.mul_apply, Pi.add_apply,
    div_eq_mul_inv, mul_inv_rev, Pi.inv_apply]
  ring

lemma psiErrorMellin_eq_continuation {s : ℂ} (hs : 1 < s.re) :
    psiErrorMellin s = psiErrorContinuation s := psiErrorMellin_eq_logDeriv_zeta hs

/-- Every zeta zero to the left of 1 gives a genuine simple pole of the continued transform. -/
theorem psiErrorContinuation_order_at_zeta_zero {z : ℂ}
    (hz : z.re < 1) (hζ : riemannZeta z = 0) :
    meromorphicOrderAt psiErrorContinuation z = ((-1 : ℤ) : WithTop ℤ) := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hζ
    norm_num at hζ
  have ha : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz1
  rw [psiErrorContinuation_eq_weighted_logDeriv]
  apply order_weighted_logDeriv_add ha.meromorphicAt
    (zeta_order_ne_zero_of_zero hz1 hζ) (zeta_order_ne_top_of_re_lt_one hz)
  · exact analyticAt_const.div analyticAt_id hz0
  · exact div_ne_zero (by norm_num) hz0
  · exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz1)

/-- Even changing the value at the pole cannot turn the continued transform into a holomorphic germ. -/
theorem no_analytic_extension_of_psiErrorContinuation_at_zeta_zero {z : ℂ}
    (hz : z.re < 1) (hζ : riemannZeta z = 0) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F z) (heq : psiErrorContinuation =ᶠ[𝓝[≠] z] F) : False := by
  have hp := psiErrorContinuation_order_at_zeta_zero hz hζ
  have he := meromorphicOrderAt_congr heq
  have hn := hF.meromorphicOrderAt_nonneg
  rw [← he, hp] at hn
  have hbad : (0 : ℤ) ≤ -1 := by exact_mod_cast hn
  omega

end LeanEval.NumberTheory.Lagarias.Landau
