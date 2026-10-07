import Playground.Lagarias.BlueprintJIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Right derivatives at prime-power endpoints

The Chebyshev sum includes its upper endpoint. It is therefore locally
constant to the right, not necessarily continuous from the left. The
right-sided fundamental theorem of calculus gives a derivative for `J`
at every point of `[2, infinity)`, without discarding the jumps of `psi`.
This is the input to the right-derivative integration-by-parts theorem.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open MeasureTheory Filter Set
open scoped Topology

lemma eventually_natFloor_eq_right {x : ℝ} (hx : 0 ≤ x) :
    ∀ᶠ y : ℝ in 𝓝[≥] x, ⌊y⌋₊ = ⌊x⌋₊ := by
  filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one x)] with y hy
  exact (Nat.floor_eq_iff (hx.trans hy.1)).mpr
    ⟨(Nat.floor_le hx).trans hy.1, hy.2⟩

lemma eventually_psi_eq_right {x : ℝ} (hx : 0 ≤ x) :
    ∀ᶠ y : ℝ in 𝓝[≥] x, Chebyshev.psi y = Chebyshev.psi x := by
  filter_upwards [eventually_natFloor_eq_right hx] with y hy
  simp only [Chebyshev.psi, hy]

lemma continuousWithinAt_psi_right {x : ℝ} (hx : 0 ≤ x) :
    ContinuousWithinAt Chebyshev.psi (Ici x) x := by
  change Tendsto Chebyshev.psi (𝓝[≥] x) (𝓝 (Chebyshev.psi x))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_psi_eq_right hx] with y hy
  exact hy.symm

@[fun_prop] lemma measurable_w : Measurable w := by
  unfold w
  fun_prop

lemma continuousWithinAt_R_w_right {x : ℝ} (hx : 1 < x) :
    ContinuousWithinAt (fun t : ℝ => R t * w t) (Ioi x) x := by
  have hR : ContinuousWithinAt R (Ici x) x := by
    change ContinuousWithinAt (fun t : ℝ => Chebyshev.psi t - t) (Ici x) x
    exact (continuousWithinAt_psi_right (zero_lt_one.trans hx).le).sub continuousWithinAt_id
  have hw : ContinuousAt w x := continuousOn_w.continuousAt (Ioi_mem_nhds hx)
  exact (hR.mul hw.continuousWithinAt).mono Ioi_subset_Ici_self

set_option backward.isDefEq.respectTransparency false in
/-- The smoothing function has the indicated right derivative, even at prime powers. -/
theorem hasDerivWithinAt_J_right {x : ℝ} (hx : 2 ≤ x) :
    HasDerivWithinAt J (-(R x * w x)) (Ioi x) x := by
  have hI : HasDerivWithinAt (fun t : ℝ => ∫ u : ℝ in 2..t, R u * w u)
      (R x * w x) (Ici x) x :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (intervalIntegrable_R_w (a := 2) le_rfl hx)
      ((measurable_R.mul measurable_w).stronglyMeasurable.stronglyMeasurableAtFilter)
      (continuousWithinAt_R_w_right (by linarith : 1 < x))
  have hJ := hI.const_sub (J 2)
  have hJ' : HasDerivWithinAt J (-(R x * w x)) (Ici x) x := by
    apply hJ.congr
    · intro y hy
      exact J_eq_sub_integral (hx.trans hy)
    · exact J_eq_sub_integral hx
  exact hJ'.mono Ioi_subset_Ici_self

end LeanEval.NumberTheory.Lagarias.Blueprint
