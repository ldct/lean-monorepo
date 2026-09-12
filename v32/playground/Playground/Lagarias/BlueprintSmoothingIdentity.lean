import Playground.Lagarias.BlueprintConverseBound
import Playground.Lagarias.BlueprintPrimePowerSum
import Mathlib.NumberTheory.AbelSummation

/-!
# The exact smoothed prime-error identity on finite intervals

Blueprint: Lemma 3.3. Abel summation proves the identity without differentiating
step functions at prime powers. Consequently all endpoint jumps are handled
by the same finite-sum theorem. No improper integral or absolute convergence
at infinity is assumed in this file.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

lemma continuousOn_w : ContinuousOn w (Set.Ioi 1) := by
  intro x hx
  change 1 < x at hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hden : x ^ 2 * Real.log x ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hl0)
  exact (by
    unfold w
    fun_prop (disch := assumption) : ContinuousAt w x).continuousWithinAt

lemma uIcc_subset_Ioi_one {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Set.uIcc a b ⊆ Set.Ioi 1 := by
  intro x hx
  have hx2 : 2 ≤ x := (le_min ha hb).trans hx.1
  change 1 < x
  linarith

lemma intervalIntegrable_psi_w {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.psi t * w t) volume a b :=
  Chebyshev.psi_mono.intervalIntegrable.mul_continuousOn
    (continuousOn_w.mono (uIcc_subset_Ioi_one ha hb))

lemma intervalIntegrable_x_w {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => t * w t) volume a b :=
  (continuous_id.intervalIntegrable a b).mul_continuousOn
    (continuousOn_w.mono (uIcc_subset_Ioi_one ha hb))

lemma intervalIntegrable_R_w {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => R t * w t) volume a b := by
  have hh := (intervalIntegrable_psi_w ha hb).sub (intervalIntegrable_x_w ha hb)
  change IntervalIntegrable (fun t => Chebyshev.psi t * w t - t * w t) volume a b at hh
  simpa only [R, sub_mul] using hh

lemma sum_Icc_h_mangoldt (x : ℝ) :
    (∑ k ∈ Icc 0 ⌊x⌋₊, h (k : ℝ) * Λ k) = B x := by
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊), B_eq_sum_Ioc_vonMangoldt]
  simp only [Nat.cast_zero, h, Real.log_zero, mul_zero, div_zero, zero_mul, zero_add]
  apply sum_congr rfl
  intro k hk
  ring

/-- Abel summation with `h(x)=1/(x log x)`, including prime-power endpoints. -/
theorem B_eq_abel_h {x : ℝ} (hx : 2 ≤ x) :
    B x = h x * Chebyshev.psi x + ∫ t : ℝ in 2..x, Chebyshev.psi t * w t := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x, DifferentiableAt ℝ h t := by
    intro t ht
    exact (hasDerivAt_h (by linarith [ht.1])).differentiableAt
  have hInt : IntegrableOn (deriv h) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => -w t) (Set.Icc 2 x) :=
      (continuousOn_w.mono (by
        intro t ht
        exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht.1)).neg
    apply hc.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro t ht
    exact (hasDerivAt_h (by linarith [ht.1])).deriv.symm
  have hab := sum_mul_eq_sub_integral_mul₁ ArithmeticFunction.vonMangoldt
    (by simp) (by simp) x hdiff hInt
  rw [sum_Icc_h_mangoldt, ← Chebyshev.psi_eq_sum_Icc] at hab
  have hIntegral : (∫ t : ℝ in Set.Ioc 2 x,
      deriv h t * ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k) =
        -(∫ t : ℝ in 2..x, Chebyshev.psi t * w t) := by
    rw [← intervalIntegral.integral_of_le hx, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    change deriv h t * (∑ k ∈ Icc 0 ⌊t⌋₊, Λ k) = -(Chebyshev.psi t * w t)
    rw [(hasDerivAt_h (by linarith [ht.1])).deriv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hIntegral] at hab
  simpa only [sub_neg_eq_add] using hab

lemma hasDerivAt_g_sub_xh {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => g t - t * h t) (x * w x) x := by
  have hd : HasDerivAt (fun t : ℝ => g t - t * h t)
      (h x - (1 * h x + x * (-w x))) x := by
    simpa only [Pi.sub_apply, Pi.mul_apply, id_eq] using
      (hasDerivAt_g hx).sub ((hasDerivAt_id x).mul (hasDerivAt_h hx))
  convert hd using 1 <;> ring

lemma integral_x_w {x : ℝ} (hx : 2 ≤ x) :
    (∫ t : ℝ in 2..x, t * w t) = (g x - x * h x) - (g 2 - 2 * h 2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (intervalIntegrable_x_w le_rfl hx)
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  exact hasDerivAt_g_sub_xh (by linarith [ht.1])

/-- The finite expression (3.7) is an indefinite integral, so no jump analysis
or absolute convergence assumption is needed to establish this identity. -/
theorem J_eq_sub_integral {x : ℝ} (hx : 2 ≤ x) :
    J x = J 2 - ∫ t : ℝ in 2..x, R t * w t := by
  have hab := B_eq_abel_h hx
  have hab2 := B_eq_abel_h (x := 2) le_rfl
  simp only [intervalIntegral.integral_same, add_zero] at hab2
  have hi := integral_x_w hx
  have hsub := intervalIntegral.integral_sub (intervalIntegrable_psi_w le_rfl hx)
    (intervalIntegrable_x_w le_rfl hx)
  have hR : (∫ t : ℝ in 2..x, R t * w t) =
      (∫ t : ℝ in 2..x, Chebyshev.psi t * w t) - ∫ t : ℝ in 2..x, t * w t := by
    simpa only [R, sub_mul] using hsub
  unfold J
  rw [hab, hab2, hR, hi]
  unfold R
  ring

/-- The exact finite-interval smoothing identity of Lemma 3.3. -/
theorem J_sub_J_eq_integral {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    J a - J b = ∫ t : ℝ in a..b, R t * w t := by
  rw [J_eq_sub_integral ha, J_eq_sub_integral hb]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_R_w (a := 2) le_rfl ha) (intervalIntegrable_R_w ha hb)
  linarith only [hadd]

end LeanEval.NumberTheory.Lagarias.Blueprint
