import Playground.Lagarias.BlueprintMertensNormalization
import Playground.Lagarias.BlueprintSmoothingIdentity

/-!
# The improper smoothed-error integral and its Mellin means

Blueprint: Lemma 3.3 and equation (10.8). The integral of `R * w` is treated
as the limit of finite interval integrals. No unconditional absolute
integrability of `R * w` is asserted. In contrast, the Mellin integrals of
`J` with positive real exponent are proved absolutely integrable.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

@[fun_prop] lemma measurable_R : Measurable R :=
  Chebyshev.psi_mono.measurable.sub measurable_id

@[fun_prop] lemma measurable_J : Measurable J := by
  unfold J g h
  fun_prop

/-- The endpoint jumps cancel because `J` is an indefinite integral. -/
theorem continuousOn_J_interval {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ContinuousOn J (uIcc a b) := by
  have hc : ContinuousOn (fun t : ℝ => J a - ∫ u : ℝ in a..t, R u * w u)
      (uIcc a b) :=
    continuousOn_const.sub (intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_R_w ha hb) left_mem_uIcc)
  apply hc.congr
  intro t ht
  have ht2 : 2 ≤ t := (le_min ha hb).trans ht.1
  linarith only [J_sub_J_eq_integral ha ht2]

lemma continuousAt_J {x : ℝ} (hx : 2 < x) : ContinuousAt J x := by
  have hc := continuousOn_J_interval (a := 2) (b := x + 1) le_rfl (by linarith)
  have hn : uIcc (2 : ℝ) (x + 1) ∈ 𝓝 x := by
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ x + 1)]
    exact Icc_mem_nhds hx (by linarith)
  exact hc.continuousAt hn

/-- Equation (3.8), with precisely the improper-integral meaning in the manuscript. -/
theorem tendsto_integral_R_w {a : ℝ} (ha : 2 ≤ a) :
    Tendsto (fun b : ℝ => ∫ x : ℝ in a..b, R x * w x) atTop (𝓝 (J a)) := by
  have ht : Tendsto (fun b : ℝ => J a - J b) atTop (𝓝 (J a)) := by
    simpa only [sub_zero] using tendsto_J_zero.const_sub (J a)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with b hb
  exact J_sub_J_eq_integral ha hb

lemma abs_J_le_uniform {x : ℝ} (hx : 2 ≤ x) :
    |J x| ≤ 22 / Real.log 2 := by
  apply (abs_J_le hx).trans
  exact div_le_div_of_nonneg_left (by norm_num) (Real.log_pos (by norm_num))
    (Real.log_le_log (by norm_num) hx)

/-- Absolute convergence of the real Mellin integral for every positive exponent. -/
theorem integrableOn_J_mellin {a v : ℝ} (ha : 2 ≤ a) (hv : 0 < v) :
    IntegrableOn (fun x : ℝ => J x * x ^ (-v - 1)) (Ioi a) := by
  have ha0 : 0 < a := by linarith
  have hm := (integrableOn_Ioi_rpow_of_lt (by linarith : -v - 1 < -1) ha0).const_mul
    (22 / Real.log 2)
  apply hm.mono' (by fun_prop)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  change a < x at hx
  have hx2 : 2 ≤ x := ha.trans hx.le
  have hx0 : 0 ≤ x := by linarith
  change ‖J x * x ^ (-v - 1)‖ ≤ (22 / Real.log 2) * x ^ (-v - 1)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)]
  exact mul_le_mul_of_nonneg_right (abs_J_le_uniform hx2) (Real.rpow_nonneg hx0 _)

/-- The actual transform satisfies the vanishing condition used to remove the pole at zero. -/
theorem tendsto_J_mellin_mean_zero {a : ℝ} (ha : 2 ≤ a) :
    Tendsto (fun v : ℝ => v * ∫ x : ℝ in Ioi a, J x * x ^ (-v - 1))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_mellin_mean_zero_of_integrable (by linarith : 1 ≤ a)
    (fun v hv => integrableOn_J_mellin ha hv) tendsto_J_zero

end LeanEval.NumberTheory.Lagarias.Blueprint
