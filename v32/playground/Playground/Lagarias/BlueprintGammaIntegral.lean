import Playground.Lagarias.BlueprintSmoothing
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The gamma integral in the Mertens normalization

Blueprint: the last paragraph of Lemma 3.2. The gamma derivative fixes the
constant in the logarithmic Mellin integral. The logarithmic change of
variables is proved directly from the general change-of-variables theorem,
including its integrability equivalence.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma log_image_Ioi {a : ℝ} (ha : 0 < a) : Real.log '' Ioi a = Ioi (Real.log a) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Real.log_lt_log ha hx
  · intro hy
    refine ⟨Real.exp y, ?_, Real.log_exp y⟩
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ < Real.exp y := Real.exp_lt_exp.mpr hy

lemma log_injOn_Ioi {a : ℝ} (ha : 0 < a) : InjOn Real.log (Ioi a) := by
  intro x hx y hy heq
  have h := congrArg Real.exp heq
  simpa only [Real.exp_log (ha.trans hx), Real.exp_log (ha.trans hy)] using h

lemma integral_log_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi a, x⁻¹ • f (Real.log x)) = ∫ y : ℝ in Ioi (Real.log a), f y := by
  have hder : ∀ x ∈ Ioi a, HasDerivWithinAt Real.log x⁻¹ (Ioi a) x :=
    fun x hx => (Real.hasDerivAt_log (ha.trans hx).ne').hasDerivWithinAt
  have hc := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder (log_injOn_Ioi ha) f
  rw [log_image_Ioi ha] at hc
  rw [hc]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change x⁻¹ • f (Real.log x) = |x⁻¹| • f (Real.log x)
  rw [abs_of_pos (inv_pos.mpr (ha.trans hx))]

lemma integrable_log_substitution_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x⁻¹ • f (Real.log x)) (Ioi a) ↔
      IntegrableOn f (Ioi (Real.log a)) := by
  have hder : ∀ x ∈ Ioi a, HasDerivWithinAt Real.log x⁻¹ (Ioi a) x :=
    fun x hx => (Real.hasDerivAt_log (ha.trans hx).ne').hasDerivWithinAt
  rw [← log_image_Ioi ha,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder (log_injOn_Ioi ha)]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro x hx
  change x⁻¹ • f (Real.log x) = |x⁻¹| • f (Real.log x)
  rw [abs_of_pos (inv_pos.mpr (ha.trans hx))]

lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · have hlog : IntegrableOn Real.log (Ioc (0 : ℝ) 1) := by
      simpa only [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
        using (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
    apply hlog.norm.mono' (by fun_prop)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (by linarith [ht.1]))
  · have hmajor := (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 1).const_mul (2 : ℝ)
    apply hmajor.mono' (by fun_prop)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change 1 < t at ht
    have ht0 : 0 < t := by linarith
    have hlog := Real.log_le_sub_one_of_pos ht0
    have he := Real.add_one_le_exp (t / 2)
    have hfirst : Real.log t ≤ 2 * Real.exp (t / 2) := by linarith
    have hbound := mul_le_mul_of_nonneg_right hfirst (Real.exp_pos (-t)).le
    have heq : (2 * Real.exp (t / 2)) * Real.exp (-t) = 2 * Real.exp ((-1 / 2) * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq] at hbound
    simpa only [norm_mul, Real.norm_of_nonneg (Real.log_nonneg ht.le),
      Real.norm_of_nonneg (Real.exp_pos _).le] using hbound

/-- The logarithmic gamma integral, with Euler's constant as defined in Mathlib. -/
theorem integral_log_mul_exp_neg :
    (∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-t)) = -Real.eulerMascheroniConstant := by
  let I : ℝ := ∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-t)
  have hd := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  have hval : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) *
      ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) = (I : ℂ) := by
    simp only [sub_self, Complex.cpow_zero, one_mul, ← Complex.ofReal_mul,
      integral_complex_ofReal, I]
  rw [hval] at hd
  have hGamma : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (0 : ℝ) < (1 : ℂ).re)] with z hz
    exact Complex.Gamma_eq_integral hz
  have heq := hGamma.unique Complex.hasDerivAt_Gamma_one
  exact_mod_cast heq

lemma scaled_log_exp_identity {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    (Real.log (v * t) - Real.log v) * Real.exp (-(v * t)) =
      Real.log t * Real.exp (-v * t) := by
  rw [Real.log_mul hv.ne' ht.ne']
  simp only [add_sub_cancel_left, neg_mul]

lemma integrableOn_log_mul_exp_scaled {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-v * t)) (Ioi 0) := by
  let F : ℝ → ℝ := fun u => (Real.log u - Real.log v) * Real.exp (-u)
  have hF : IntegrableOn F (Ioi 0) := by
    have hh := integrableOn_log_mul_exp_neg.sub ((integrableOn_exp_neg_Ioi 0).const_mul (Real.log v))
    change IntegrableOn (fun u => Real.log u * Real.exp (-u) - Real.log v * Real.exp (-u)) (Ioi 0) at hh
    simpa only [F, sub_mul] using hh
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff F 0 hv).mpr (by simpa using hF)
  apply hcomp.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact scaled_log_exp_identity hv ht

lemma integral_log_mul_exp_scaled {v : ℝ} (hv : 0 < v) :
    (∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-v * t)) =
      v⁻¹ * (-Real.eulerMascheroniConstant - Real.log v) := by
  let F : ℝ → ℝ := fun u => (Real.log u - Real.log v) * Real.exp (-u)
  have hscaled := integral_comp_mul_left_Ioi F 0 hv
  have hleft : (∫ t : ℝ in Ioi 0, F (v * t)) =
      ∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-v * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact scaled_log_exp_identity hv ht
  rw [hleft] at hscaled
  have hright : (∫ t : ℝ in Ioi 0, F t) = -Real.eulerMascheroniConstant - Real.log v := by
    simp only [F, sub_mul]
    rw [integral_sub integrableOn_log_mul_exp_neg ((integrableOn_exp_neg_Ioi 0).const_mul _),
      integral_log_mul_exp_neg, integral_const_mul, integral_exp_neg_Ioi]
    simp
  simpa only [mul_zero, smul_eq_mul, hright] using hscaled

lemma log_mellin_kernel_eq {v x : ℝ} (hx : 1 < x) :
    x⁻¹ * (Real.log (Real.log x) * Real.exp (-v * Real.log x)) = g x * x ^ (-v - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp : x ^ (-v - 1) = x⁻¹ * Real.exp (-v * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0,
      show Real.log x * (-v - 1) = -Real.log x + (-v * Real.log x) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hx0]
  rw [hp]
  unfold g
  ring

lemma integrableOn_g_mellin {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun x : ℝ => g x * x ^ (-v - 1)) (Ioi 1) := by
  have hh := (integrable_log_substitution_iff
    (fun t : ℝ => Real.log t * Real.exp (-v * t)) (a := 1) zero_lt_one).mpr
      (by simpa using integrableOn_log_mul_exp_scaled hv)
  apply hh.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact log_mellin_kernel_eq hx

/-- The exact main term used to identify the prime-power Mertens constant. -/
theorem mellin_g_eq {v : ℝ} (hv : 0 < v) :
    v * (∫ x : ℝ in Ioi 1, g x * x ^ (-v - 1)) =
      -Real.log v - Real.eulerMascheroniConstant := by
  have hh := integral_log_substitution
    (fun t : ℝ => Real.log t * Real.exp (-v * t)) (a := 1) zero_lt_one
  have hleft : (∫ x : ℝ in Ioi 1, x⁻¹ •
      (Real.log (Real.log x) * Real.exp (-v * Real.log x))) =
        ∫ x : ℝ in Ioi 1, g x * x ^ (-v - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact log_mellin_kernel_eq hx
  rw [hleft, Real.log_one, integral_log_mul_exp_scaled hv] at hh
  rw [hh]
  field_simp
  ring

end LeanEval.NumberTheory.Lagarias.Blueprint
