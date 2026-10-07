import Playground.Lagarias.BlueprintMellinDensities
import Playground.Lagarias.BlueprintZetaRegular
import Playground.Lagarias.LandauZeta
import Mathlib.Tactic.LinearCombination

/-!
# The actual prime-error transform and its continuation

Blueprint: equation (10.3). The infinite integral is identified with the
proved logarithmic-derivative expression on its initial convergence
half-plane. The subtracted finite interval is proved entire. The analytic
representative at zero is the genuine pole-removed zeta function.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma primeErrorDensity_kernel_shift {x : ℝ} (hx : 0 < x) (s : ℂ) :
    primeErrorDensity x * (x : ℂ) ^ (-s - 1) =
      ((R x : ℝ) : ℂ) * (x : ℂ) ^ (-((s + 1) + 1)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold primeErrorDensity
  rw [Complex.ofReal_div, show -s - 1 = -(s + 1) by ring,
    ← Landau.mul_cpow_kernel hx (s + 1)]
  field_simp

lemma QIntegral_one_eq_psiErrorMellin (s : ℂ) :
    QIntegral 1 s = Landau.psiErrorMellin (s + 1) := by
  rw [QIntegral, truncatedMellin_eq_integral (by norm_num : (0 : ℝ) ≤ 1)]
  unfold Landau.psiErrorMellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change primeErrorDensity x * (x : ℂ) ^ (-s - 1) =
    ((Chebyshev.psi x - x : ℝ) : ℂ) * (x : ℂ) ^ (-((s + 1) + 1))
  exact primeErrorDensity_kernel_shift (zero_lt_one.trans hx) s

/-- Identification on the actual half-plane of initial convergence. -/
lemma QIntegral_one_eq_QRegular {s : ℂ} (hs : 0 < s.re) :
    QIntegral 1 s = QRegular s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hs' : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hs1 : s + 1 ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  calc
    QIntegral 1 s = Landau.psiErrorMellin (s + 1) := QIntegral_one_eq_psiErrorMellin s
    _ = Landau.psiErrorContinuation (s + 1) := Landau.psiErrorMellin_eq_logDeriv_zeta hs'
    _ = QRegular s := (QRegular_eq_psiErrorContinuation hs0 hs1
      (riemannZeta_ne_zero_of_one_lt_re hs')).symm

noncomputable def QCutoff (a : ℝ) : ℂ → ℂ :=
  truncatedMellin 1 (upperCutoff a primeErrorDensity)

lemma differentiable_QCutoff (a : ℝ) : Differentiable ℂ (QCutoff a) := by
  apply differentiable_finiteCutoffMellin (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 8) measurable_primeErrorDensity
  intro x hx hxa
  exact primeErrorDensity_bound (zero_lt_one.trans hx)

lemma QCutoff_eq_integral {a : ℝ} (ha : 1 ≤ a) (s : ℂ) :
    QCutoff a s = ∫ x : ℝ in 1..a, primeErrorDensity x * (x : ℂ) ^ (-s - 1) := by
  rw [QCutoff, finiteCutoffMellin_eq_integral (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le ha]

/-- The continuation uses an analytic representative even at the removed point zero. -/
noncomputable def QContinuation (a : ℝ) (s : ℂ) : ℂ := QRegular s - QCutoff a s

lemma meromorphic_QContinuation (a : ℝ) : MeromorphicOn (QContinuation a) univ :=
  fun s _ => (meromorphic_QRegular s (mem_univ _)).sub
    ((differentiable_QCutoff a).analyticAt s).meromorphicAt

lemma analyticAt_QContinuation_real (a : ℝ) {t : ℝ} (ht : -(1 / 2) < t) :
    AnalyticAt ℂ (QContinuation a) (t : ℂ) :=
  (analyticAt_QRegular_real ht).sub ((differentiable_QCutoff a).analyticAt (t : ℂ))

/-- Equation (10.3), with the infinite integral and finite correction both justified. -/
theorem QIntegral_eq_QContinuation {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    QIntegral a s = QContinuation a s := by
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_QIntegral (a := 1) le_rfl hs) (integrableOn_QIntegral ha hs)
  have h1 : (∫ x : ℝ in Ioi 1, primeErrorDensity x * (x : ℂ) ^ (-s - 1)) = QIntegral 1 s :=
    (truncatedMellin_eq_integral (by norm_num : (0 : ℝ) ≤ 1) primeErrorDensity s).symm
  have ha' : (∫ x : ℝ in Ioi a, primeErrorDensity x * (x : ℂ) ^ (-s - 1)) = QIntegral a s :=
    (truncatedMellin_eq_integral (zero_le_one.trans ha) primeErrorDensity s).symm
  rw [← QCutoff_eq_integral ha s, h1, ha', QIntegral_one_eq_QRegular hs] at hsplit
  unfold QContinuation
  linear_combination hsplit

/-- The differential right-hand side is analytic near every required real point. -/
theorem analyticAt_QContinuation_sub_deriv_real (a : ℝ) {t : ℝ} (ht : -(1 / 2) < t) :
    AnalyticAt ℂ (fun s : ℂ => QContinuation a s - deriv (QContinuation a) s) (t : ℂ) :=
  (analyticAt_QContinuation_real a ht).sub (analyticAt_QContinuation_real a ht).deriv

/-- The differential relation initially holds for the continued Q, not an unrelated function. -/
theorem deriv_deriv_WIntegral_eq_QContinuation {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    deriv (deriv (WIntegral a)) s = QContinuation a s - deriv (QContinuation a) s := by
  have ha1 : 1 ≤ a := by linarith
  have heq : QIntegral a =ᶠ[𝓝 s] QContinuation a := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact QIntegral_eq_QContinuation ha1 hz
  rw [deriv_deriv_WIntegral ha hs, QIntegral_eq_QContinuation ha1 hs, heq.deriv_eq]

end LeanEval.NumberTheory.Lagarias.Blueprint
