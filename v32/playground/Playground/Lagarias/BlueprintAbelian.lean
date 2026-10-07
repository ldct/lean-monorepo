import Playground.Lagarias.BlueprintGammaIntegral

/-!
# An Abelian limit for Mellin averages

Blueprint: the normalization in Lemma 3.2 and the removal of the singularity
in Lemma 10.3. A bounded measurable function tending to zero has vanishing
Mellin mean `v * integral_a^infty f(x) x^(-v-1)` as positive v tends to zero.
The proof splits into a finite interval and a uniformly small tail. Neither
interchanging a divergent integral nor an unproved Tauberian theorem is used.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma mellin_kernel_integral {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    (∫ x : ℝ in Ioi a, x ^ (-v - 1)) = a ^ (-v) / v := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -v - 1 < -1) ha,
    show -v - 1 + 1 = -v by ring, neg_div_neg_eq]

lemma mellin_kernel_le_one {x v : ℝ} (hx : 1 ≤ x) (hv : 0 < v) :
    x ^ (-v - 1) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)

lemma integrableOn_bounded_mellin {f : ℝ → ℝ} {a M v : ℝ} (ha : 1 ≤ a)
    (hf : Measurable f) (hbound : ∀ x : ℝ, a < x → |f x| ≤ M) (hv : 0 < v) :
    IntegrableOn (fun x => f x * x ^ (-v - 1)) (Ioi a) := by
  have hmajor := (integrableOn_Ioi_rpow_of_lt (by linarith : -v - 1 < -1)
    (by linarith : 0 < a)).const_mul M
  apply hmajor.mono' (by fun_prop)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := by linarith [show a < x from hx]
  change ‖f x * x ^ (-v - 1)‖ ≤ M * x ^ (-v - 1)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)]
  exact mul_le_mul_of_nonneg_right (hbound x hx) (Real.rpow_nonneg hx0 _)

lemma abs_mellin_mean_le {f : ℝ → ℝ} {a M v : ℝ} (ha : 1 ≤ a)
    (hM : 0 ≤ M) (hbound : ∀ x : ℝ, a < x → |f x| ≤ M) (hv : 0 < v) :
    |v * (∫ x : ℝ in Ioi a, f x * x ^ (-v - 1))| ≤ M := by
  have hmajor := (integrableOn_Ioi_rpow_of_lt (by linarith : -v - 1 < -1)
    (by linarith : 0 < a)).const_mul M
  have hboundAE : ∀ᵐ x : ℝ ∂volume.restrict (Ioi a),
      ‖f x * x ^ (-v - 1)‖ ≤ M * x ^ (-v - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := by linarith [show a < x from hx]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (Real.rpow_nonneg hx0 _)
  have hnorm := norm_integral_le_of_norm_le hmajor hboundAE
  rw [integral_const_mul, mellin_kernel_integral (by linarith : 0 < a) hv] at hnorm
  rw [abs_mul, abs_of_pos hv]
  calc
    v * |∫ x : ℝ in Ioi a, f x * x ^ (-v - 1)| ≤ v * (M * (a ^ (-v) / v)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hnorm) hv.le
    _ = M * a ^ (-v) := by field_simp
    _ ≤ M := mul_le_of_le_one_right hM (Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith))

/-- A locally finite, uniformly bounded error tending to zero has vanishing
Mellin mean. The positive-side approach to zero is explicit. -/
theorem tendsto_mellin_mean_zero {f : ℝ → ℝ} {a M : ℝ} (ha : 1 ≤ a)
    (hf : Measurable f) (hM : 0 ≤ M) (hbound : ∀ x : ℝ, a < x → |f x| ≤ M)
    (hlim : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun v : ℝ => v * ∫ x : ℝ in Ioi a, f x * x ^ (-v - 1)) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  let A : ℝ := max a N + 1
  have hAa : a ≤ A := by dsimp [A]; linarith [le_max_left a N]
  have hAN : N ≤ A := by dsimp [A]; linarith [le_max_right a N]
  have hA1 : 1 ≤ A := ha.trans hAa
  have htail : ∀ x : ℝ, A < x → |f x| ≤ ε / 2 := by
    intro x hx
    simpa only [dist_zero_right, Real.norm_eq_abs] using (hN x (hAN.trans hx.le)).le
  let C : ℝ := M * |A - a|
  have hC : 0 ≤ C := mul_nonneg hM (abs_nonneg _)
  have hsmallLimit : Tendsto (fun v : ℝ => v * C) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).mul_const C :
      Tendsto (fun v : ℝ => v * C) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) * C)))
  have hsmall : ∀ᶠ v : ℝ in 𝓝[>] 0, v * C < ε / 2 :=
    hsmallLimit.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hsmall] with v hv hvC
  change 0 < v at hv
  have haInt := integrableOn_bounded_mellin ha hf hbound hv
  have hAInt := integrableOn_bounded_mellin hA1 hf htail hv
  have hsplit := intervalIntegral.integral_interval_add_Ioi haInt hAInt
  have hcompact : |∫ x : ℝ in a..A, f x * x ^ (-v - 1)| ≤ C := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := M)
      (a := a) (b := A) (f := fun x => f x * x ^ (-v - 1)) (fun x hx => ?_)
    · simpa only [Real.norm_eq_abs, C] using hh
    · rw [Set.uIoc_of_le hAa] at hx
      have hx1 : 1 ≤ x := ha.trans hx.1.le
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      calc
        |f x| * x ^ (-v - 1) ≤ M * x ^ (-v - 1) :=
          mul_le_mul_of_nonneg_right (hbound x hx.1) (Real.rpow_nonneg (by linarith) _)
        _ ≤ M := mul_le_of_le_one_right hM (mellin_kernel_le_one hx1 hv)
  have htailMean := abs_mellin_mean_le hA1 (half_pos hε).le htail hv
  simp only [dist_zero_right, Real.norm_eq_abs]
  rw [← hsplit, mul_add]
  calc
    |v * (∫ x : ℝ in a..A, f x * x ^ (-v - 1)) +
        v * ∫ x : ℝ in Ioi A, f x * x ^ (-v - 1)| ≤
        |v * (∫ x : ℝ in a..A, f x * x ^ (-v - 1))| +
          |v * ∫ x : ℝ in Ioi A, f x * x ^ (-v - 1)| := abs_add_le _ _
    _ ≤ v * C + ε / 2 := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos hv]
        exact mul_le_mul_of_nonneg_left hcompact hv.le
      · exact htailMean
    _ < ε := by linarith

end LeanEval.NumberTheory.Lagarias.Blueprint
