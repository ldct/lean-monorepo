import Playground.Lagarias.BlueprintZetaReal
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The removable point of the prime-error continuation

Mathlib already proves that the pole-removed function `riemannZeta₁` is
entire, equals `(s-1) zeta(s)` away from one, and has value one there.
We reuse that theorem rather than recompute the gamma-factor extension.
Its logarithmic derivative supplies a genuinely analytic representative
of the prime-error continuation at `s=0`.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Filter Set
open scoped Topology

/-- The genuine entire extension, not the product's junk value at the pole. -/
noncomputable def regularizedZeta : ℂ → ℂ := riemannZeta₁

lemma differentiable_regularizedZeta : Differentiable ℂ regularizedZeta :=
  differentiable_riemannZeta₁

lemma regularizedZeta_eq_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    regularizedZeta s = (s - 1) * riemannZeta s := riemannZeta₁_of_ne hs

lemma regularizedZeta_one : regularizedZeta 1 = 1 := riemannZeta₁_one

/-- The entire extension of `s * zeta(s+1)`. -/
noncomputable def zetaPoleRemoved (s : ℂ) : ℂ := regularizedZeta (s + 1)

lemma differentiable_zetaPoleRemoved : Differentiable ℂ zetaPoleRemoved :=
  differentiable_regularizedZeta.comp (by fun_prop)

@[simp] lemma zetaPoleRemoved_zero : zetaPoleRemoved 0 = 1 := by
  simp only [zetaPoleRemoved, zero_add, regularizedZeta_one]

lemma zetaPoleRemoved_eq {s : ℂ} (hs : s ≠ 0) :
    zetaPoleRemoved s = s * riemannZeta (s + 1) := by
  have hs1 : s + 1 ≠ 1 := by simpa using hs
  simpa only [zetaPoleRemoved, add_sub_cancel_right] using regularizedZeta_eq_mul_zeta hs1

set_option backward.isDefEq.respectTransparency false in
lemma hasDerivAt_zetaPoleRemoved {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt zetaPoleRemoved (riemannZeta (s + 1) + s * deriv riemannZeta (s + 1)) s := by
  have hs1 : s + 1 ≠ 1 := by simpa using hs
  have hz : HasDerivAt (fun z : ℂ => riemannZeta (z + 1)) (deriv riemannZeta (s + 1)) s := by
    convert! (differentiableAt_riemannZeta hs1).hasDerivAt.comp s ((hasDerivAt_id s).add_const 1) using 1 <;>
      simp only [mul_one]
  have hm : HasDerivAt (fun z : ℂ => z * riemannZeta (z + 1))
      (riemannZeta (s + 1) + s * deriv riemannZeta (s + 1)) s := by
    convert! (hasDerivAt_id s).mul hz using 1 <;> simp only [id_eq, one_mul]
  apply hm.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact zetaPoleRemoved_eq hz

/-- The regularized prime-error transform before subtracting the finite cutoff. -/
noncomputable def QRegular (s : ℂ) : ℂ := -(logDeriv zetaPoleRemoved s + 1) / (s + 1)

lemma QRegular_eq_psiErrorContinuation {s : ℂ} (hs : s ≠ 0)
    (hs1 : s + 1 ≠ 0) (hz : riemannZeta (s + 1) ≠ 0) :
    QRegular s = Landau.psiErrorContinuation (s + 1) := by
  unfold QRegular logDeriv Landau.psiErrorContinuation
  simp only [Pi.div_apply]
  rw [(hasDerivAt_zetaPoleRemoved hs).deriv, zetaPoleRemoved_eq hs]
  simp only [add_sub_cancel_right]
  field_simp
  ring

lemma analyticAt_QRegular {s : ℂ} (hs : s + 1 ≠ 0) (hz : zetaPoleRemoved s ≠ 0) :
    AnalyticAt ℂ QRegular s := by
  have hf := differentiable_zetaPoleRemoved.analyticAt s
  change AnalyticAt ℂ (fun z : ℂ => -(deriv zetaPoleRemoved z / zetaPoleRemoved z + 1) / (z + 1)) s
  exact ((hf.deriv.div hf hz).add analyticAt_const).neg.div
    (analyticAt_id.add analyticAt_const) hs

lemma meromorphic_QRegular : MeromorphicOn QRegular univ := by
  intro s hs
  have hf := differentiable_zetaPoleRemoved.analyticAt s
  change MeromorphicAt (fun z : ℂ => -(deriv zetaPoleRemoved z / zetaPoleRemoved z + 1) / (z + 1)) s
  exact ((hf.deriv.meromorphicAt.div hf.meromorphicAt).add (analyticAt_const.meromorphicAt)).neg.div
    ((analyticAt_id.add analyticAt_const).meromorphicAt)

/-- The apparent singularity at zero is removed, and every real point
strictly to the right of `-1/2` has an analytic neighborhood. -/
theorem analyticAt_QRegular_real {t : ℝ} (ht : -(1 / 2) < t) :
    AnalyticAt ℂ QRegular (t : ℂ) := by
  have ht1 : (1 / 2 : ℝ) < t + 1 := by linarith
  have hs1 : (t : ℂ) + 1 ≠ 0 := by
    intro heq
    have hr := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  apply analyticAt_QRegular hs1
  by_cases ht0 : t = 0
  · subst t
    simp
  · have hs0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    rw [zetaPoleRemoved_eq hs0]
    apply mul_ne_zero hs0
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using riemannZeta_ne_zero_real_gt_half ht1

end LeanEval.NumberTheory.Lagarias.Blueprint
