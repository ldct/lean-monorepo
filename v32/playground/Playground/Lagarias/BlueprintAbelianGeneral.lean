import Playground.Lagarias.BlueprintAbelian

/-!
# Mellin means with an integrable singularity at the lower endpoint

For the Mertens normalization, the error includes `log log x`, which is
unbounded near x=1. We therefore do not apply a globally bounded-error lemma
there. The existing convergent Mellin integral at v=1 supplies a compact-interval
majorant, and the limiting error is small on the tail. This proves the needed
Abelian limit without concealing the endpoint singularity.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma compact_mellin_kernel_bound {f : ℝ → ℝ} {a b v x : ℝ}
    (ha : 1 ≤ a) (hx : x ∈ Ioc a b) (hv : 0 < v) :
    ‖f x * x ^ (-v - 1)‖ ≤ b ^ 2 * ‖f x * x ^ (-2 : ℝ)‖ := by
  have hx1 : 1 ≤ x := ha.trans hx.1.le
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hpow : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.rpow_two]
  have hfactor : |f x| = x ^ 2 * |f x * x ^ (-2 : ℝ)| := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _), hpow]
    field_simp
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  calc
    |f x| * x ^ (-v - 1) ≤ |f x| :=
      mul_le_of_le_one_right (abs_nonneg _) (mellin_kernel_le_one hx1 hv)
    _ = x ^ 2 * |f x * x ^ (-2 : ℝ)| := hfactor
    _ ≤ b ^ 2 * ‖f x * x ^ (-2 : ℝ)‖ := by
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0.le hx.2 2) (abs_nonneg _)

/-- An integrable error tending to zero has vanishing Mellin mean, even when
it is unbounded near the finite lower endpoint. -/
theorem tendsto_mellin_mean_zero_of_integrable {f : ℝ → ℝ} {a : ℝ} (ha : 1 ≤ a)
    (hconv : ∀ v : ℝ, 0 < v → IntegrableOn (fun x => f x * x ^ (-v - 1)) (Ioi a))
    (hlim : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun v : ℝ => v * ∫ x : ℝ in Ioi a, f x * x ^ (-v - 1)) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  let b : ℝ := max a N + 1
  have hba : a ≤ b := by dsimp [b]; linarith [le_max_left a N]
  have hbN : N ≤ b := by dsimp [b]; linarith [le_max_right a N]
  have hb1 : 1 ≤ b := ha.trans hba
  have htail : ∀ x : ℝ, b < x → |f x| ≤ ε / 2 := by
    intro x hx
    simpa only [dist_zero_right, Real.norm_eq_abs] using (hN x (hbN.trans hx.le)).le
  have hbase : IntegrableOn (fun x => f x * x ^ (-2 : ℝ)) (Ioi a) := by
    simpa using hconv 1 (by norm_num)
  have hbaseCompact : IntegrableOn (fun x => f x * x ^ (-2 : ℝ)) (Ioc a b) :=
    hbase.mono_set Ioc_subset_Ioi_self
  let C : ℝ := b ^ 2 * ∫ x : ℝ in Ioc a b, ‖f x * x ^ (-2 : ℝ)‖
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  have hsmallLimit : Tendsto (fun v : ℝ => v * C) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).mul_const C :
      Tendsto (fun v : ℝ => v * C) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) * C)))
  have hsmall : ∀ᶠ v : ℝ in 𝓝[>] 0, v * C < ε / 2 :=
    hsmallLimit.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hsmall] with v hv hvC
  change 0 < v at hv
  have haInt := hconv v hv
  have hbInt : IntegrableOn (fun x => f x * x ^ (-v - 1)) (Ioi b) :=
    haInt.mono_set (Ioi_subset_Ioi hba)
  have hsplit := intervalIntegral.integral_interval_add_Ioi haInt hbInt
  have hcompact : |∫ x : ℝ in a..b, f x * x ^ (-v - 1)| ≤ C := by
    rw [intervalIntegral.integral_of_le hba]
    have hmajor := hbaseCompact.norm.const_mul (b ^ 2)
    have hpoint : ∀ᵐ x : ℝ ∂volume.restrict (Ioc a b),
        ‖f x * x ^ (-v - 1)‖ ≤ b ^ 2 * ‖f x * x ^ (-2 : ℝ)‖ := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      exact compact_mellin_kernel_bound ha hx hv
    have hh := norm_integral_le_of_norm_le hmajor hpoint
    rw [integral_const_mul] at hh
    simpa only [C, Real.norm_eq_abs] using hh
  have htailMean := abs_mellin_mean_le hb1 (half_pos hε).le htail hv
  simp only [dist_zero_right, Real.norm_eq_abs]
  rw [← hsplit, mul_add]
  calc
    |v * (∫ x : ℝ in a..b, f x * x ^ (-v - 1)) +
        v * ∫ x : ℝ in Ioi b, f x * x ^ (-v - 1)| ≤
        |v * (∫ x : ℝ in a..b, f x * x ^ (-v - 1))| +
          |v * ∫ x : ℝ in Ioi b, f x * x ^ (-v - 1)| := abs_add_le _ _
    _ ≤ v * C + ε / 2 := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos hv]
        exact mul_le_mul_of_nonneg_left hcompact hv.le
      · exact htailMean
    _ < ε := by linarith

end LeanEval.NumberTheory.Lagarias.Blueprint
