import Playground.Lagarias.BlueprintMertensSecond
import Playground.Lagarias.BlueprintLogZetaMellin
import Playground.Lagarias.BlueprintAbelianGeneral
import Playground.Lagarias.BlueprintConverseBound

/-!
# Normalization of the smoothed prime error

Blueprint: the end of Lemma 3.2 and the limit assertion in Lemma 3.3.
The previously defined Mertens constant is identified with Mathlib's actual
Euler-Mascheroni constant using the convergent logarithmic zeta integral,
the logarithmic gamma integral, an Abelian limit, and zeta's residue at 1.
In particular, the normalization is a theorem, not a definition or an axiom.

The resulting bound and limit for `J` use its exact finite expression (3.7).
The improper-integral identity for `J` is a separate subsequent result.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma integrableOn_secondError_mellin {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun x : ℝ => secondError x * x ^ (-v - 1)) (Ioi 1) := by
  have hB := integrableOn_B_mellin hv
  have hg := integrableOn_g_mellin hv
  have hc := (integrableOn_Ioi_rpow_of_lt (by linarith : -v - 1 < -1) zero_lt_one).const_mul mertensConstant
  have hh := (hB.sub hg).sub hc
  change IntegrableOn (fun x => B x * x ^ (-v - 1) - g x * x ^ (-v - 1) -
    mertensConstant * x ^ (-v - 1)) (Ioi 1) at hh
  simpa only [secondError, sub_mul] using hh

lemma secondError_mellin_identity {v : ℝ} (hv : 0 < v) :
    v * (∫ x : ℝ in Ioi 1, secondError x * x ^ (-v - 1)) =
      Real.log (riemannZeta ((1 + v : ℝ) : ℂ)).re + Real.log v +
        Real.eulerMascheroniConstant - mertensConstant := by
  have hB := integrableOn_B_mellin hv
  have hg := integrableOn_g_mellin hv
  have hc := (integrableOn_Ioi_rpow_of_lt (by linarith : -v - 1 < -1) zero_lt_one).const_mul mertensConstant
  have hsplit : (∫ x : ℝ in Ioi 1, secondError x * x ^ (-v - 1)) =
      (∫ x : ℝ in Ioi 1, B x * x ^ (-v - 1)) -
        (∫ x : ℝ in Ioi 1, g x * x ^ (-v - 1)) - mertensConstant / v := by
    simp only [secondError, sub_mul]
    rw [integral_sub (hB.sub hg) hc, integral_sub hB hg, integral_const_mul,
      mellin_kernel_integral zero_lt_one hv, Real.one_rpow]
    ring
  rw [hsplit, mul_sub, mul_sub, ← log_zeta_eq_mellin_B hv, mellin_g_eq hv]
  field_simp
  ring

lemma tendsto_zeta_residue_real :
    Tendsto (fun v : ℝ => v * (riemannZeta ((1 + v : ℝ) : ℂ)).re) (𝓝[>] 0) (𝓝 1) := by
  have harg : Tendsto (fun v : ℝ => ((1 + v : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun v : ℝ => ((1 + v : ℝ) : ℂ)) := by fun_prop
      simpa using hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      change 0 < v at hv
      change ((1 + v : ℝ) : ℂ) ≠ 1
      intro heq
      have heqR : 1 + v = (1 : ℝ) := by exact_mod_cast heq
      linarith
  have hres := riemannZeta_residue_one.comp harg
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp hres
  simpa only [Function.comp_apply, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_self,
    zero_mul, sub_zero, add_sub_cancel_left] using hre

lemma tendsto_log_zeta_add_log :
    Tendsto (fun v : ℝ => Real.log (riemannZeta ((1 + v : ℝ) : ℂ)).re + Real.log v)
      (𝓝[>] 0) (𝓝 0) := by
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp tendsto_zeta_residue_real
  have heq : (fun v : ℝ => Real.log (v * (riemannZeta ((1 + v : ℝ) : ℂ)).re)) =ᶠ[𝓝[>] 0]
      (fun v : ℝ => Real.log (riemannZeta ((1 + v : ℝ) : ℂ)).re + Real.log v) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    change 0 < v at hv
    have hz := riemannZeta_re_pos_of_one_lt (show 1 < 1 + v by linarith)
    rw [Real.log_mul hv.ne' hz.ne', add_comm]
  rw [Filter.tendsto_congr' heq] at hlog
  simpa only [Real.log_one] using hlog

/-- The essential constant-identification step in Lemma 3.2. -/
theorem mertensConstant_eq_gamma : mertensConstant = Real.eulerMascheroniConstant := by
  have hzero := tendsto_mellin_mean_zero_of_integrable (a := 1) (by norm_num)
    (fun v hv => integrableOn_secondError_mellin hv) tendsto_secondError
  have heq : (fun v : ℝ => v * ∫ x : ℝ in Ioi 1, secondError x * x ^ (-v - 1)) =ᶠ[𝓝[>] 0]
      (fun v : ℝ => Real.log (riemannZeta ((1 + v : ℝ) : ℂ)).re + Real.log v +
        Real.eulerMascheroniConstant - mertensConstant) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact secondError_mellin_identity hv
  rw [Filter.tendsto_congr' heq] at hzero
  have hconstant := (tendsto_log_zeta_add_log.add_const Real.eulerMascheroniConstant).sub_const mertensConstant
  have he := tendsto_nhds_unique hconstant hzero
  linarith

/-- Prime-power Mertens estimate with the constant fully identified. -/
theorem abs_B_sub_g_gamma_le {x : ℝ} (hx : 2 ≤ x) :
    |B x - g x - Real.eulerMascheroniConstant| ≤ 14 / Real.log x := by
  simpa only [secondError, mertensConstant_eq_gamma] using abs_secondError_le hx

lemma J_eq_hR_sub_secondError (x : ℝ) : J x = h x * R x - secondError x := by
  unfold J secondError
  rw [mertensConstant_eq_gamma]
  ring

lemma abs_R_le_eight_mul {x : ℝ} (hx : 0 ≤ x) : |R x| ≤ 8 * x := by
  have hpsi := Chebyshev.psi_le_const_mul_self hx
  have hnonneg := Chebyshev.psi_nonneg x
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  unfold R
  rw [abs_le]
  constructor <;> nlinarith

/-- The unconditional `O(1/log x)` estimate for the exact smoothing expression. -/
theorem abs_J_le {x : ℝ} (hx : 2 ≤ x) : |J x| ≤ 22 / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hh : 0 < h x := h_pos (by linarith)
  have hR : |h x * R x| ≤ 8 / Real.log x := by
    rw [abs_mul, abs_of_pos hh]
    calc
      h x * |R x| ≤ h x * (8 * x) := mul_le_mul_of_nonneg_left (abs_R_le_eight_mul hx0.le) hh.le
      _ = 8 / Real.log x := by unfold h; field_simp
  rw [J_eq_hR_sub_secondError]
  exact (abs_sub _ _).trans ((add_le_add hR (abs_secondError_le hx)).trans_eq (by ring))

/-- The normalization needed for the improper integral and the removal at s=0. -/
theorem tendsto_J_zero : Tendsto J atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_ge_atTop (2 : ℝ) |>.mono fun x hx => ?_)
    (show Tendsto (fun x : ℝ => 22 / Real.log x) atTop (𝓝 0) by
      simpa [div_eq_mul_inv] using Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (22 : ℝ))
  simpa only [Real.norm_eq_abs] using abs_J_le hx

end LeanEval.NumberTheory.Lagarias.Blueprint
