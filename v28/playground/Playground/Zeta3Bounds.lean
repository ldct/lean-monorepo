import Mathlib

set_option maxHeartbeats 4000000

open Real Finset Filter Topology

/-!
# Upper and Lower bound for ζ(3)

## Key theorems

- `zeta3_lo` : `(1.2020 : ℝ) ≤ (riemannZeta 3).re`
- `zeta3_hi` : `(riemannZeta 3).re ≤ 1.2021`

## Strategy

We use Euler-Maclaurin style bounds. Both sequences are purely rational and
converge to ζ(3): the lower bound is increasing, the upper bound is decreasing.
At N = 23 we verify the numerical bounds via `norm_num` on ℚ.
-/

namespace Zeta3Bounds

/-! ## Connection to a real-valued tsum -/

lemma summable_inv_cube_real :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    (Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 3) 1).mpr h).congr
    (fun n => by congr 1; push_cast; ring)

private lemma summable_inv_cube_cpow :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (3 : ℂ)) := by
  have hrec : 1 < (3 : ℂ).re := by simp
  rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (3 : ℂ)) =
    (fun n : ℕ => 1 / (n : ℂ) ^ (3 : ℂ)) ∘ (· + 1) from by ext; simp]
  exact (Complex.summable_one_div_nat_cpow.mpr hrec).comp_injective (fun _ _ h => by omega)

lemma zeta3_re_eq_tsum :
    (riemannZeta 3).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 := by
  have hrec : 1 < (3 : ℂ).re := by simp
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hrec
  have hterm_re : ∀ n : ℕ, (1 / ((n : ℂ) + 1) ^ (3 : ℂ)).re = 1 / ((n : ℝ) + 1) ^ 3 := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [show ((n : ℂ) + 1) ^ (3 : ℂ) = ((((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) from by
      rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) from by norm_cast, Complex.cpow_natCast]; push_cast; ring]
    rw [show (1 : ℂ) / ((((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) = ((1 / ((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) from by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [hzeta, Complex.re_tsum summable_inv_cube_cpow]
  congr 1; ext n; exact hterm_re n

lemma tendsto_partial_sum_inv_cube :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 3)
      atTop (𝓝 (riemannZeta 3).re) := by
  rw [← hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  rw [zeta3_re_eq_tsum]; exact summable_inv_cube_real.hasSum

/-! ## Define the bounding sequences -/

noncomputable def ζ_lo (N : ℕ) : ℝ :=
  (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) +
    1 / (2 * (N : ℝ) ^ 2) + 1 / (2 * (N : ℝ) ^ 3)

noncomputable def ζ_hi (N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) +
    1 / (2 * (N : ℝ) ^ 2)

/-! ## Rational fraction identities

The key analytical content: clearing denominators and verifying polynomial identities.
-/

private lemma lo_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x ^ 3 + 1 / (2 * (x + 1) ^ 2) + 1 / (2 * (x + 1) ^ 3) -
    1 / (2 * x ^ 2) - 1 / (2 * x ^ 3) =
    (2 * x + 1) / (2 * x ^ 3 * (x + 1) ^ 3) := by
  rw [eq_div_iff (by positivity : 2 * x ^ 3 * (x + 1) ^ 3 ≠ 0)]
  have e1 : 1 / x ^ 3 * (2 * x ^ 3 * (x + 1) ^ 3) = 2 * (x + 1) ^ 3 := by
    rw [one_div, show 2 * x ^ 3 * (x + 1) ^ 3 = x ^ 3 * (2 * (x + 1) ^ 3) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (2 * (x + 1) ^ 2) * (2 * x ^ 3 * (x + 1) ^ 3) = x ^ 3 * (x + 1) := by
    rw [one_div, show 2 * x ^ 3 * (x + 1) ^ 3 = (2 * (x + 1) ^ 2) * (x ^ 3 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ 3) * (2 * x ^ 3 * (x + 1) ^ 3) = x ^ 3 := by
    rw [one_div, show 2 * x ^ 3 * (x + 1) ^ 3 = (2 * (x + 1) ^ 3) * x ^ 3 from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / (2 * x ^ 2) * (2 * x ^ 3 * (x + 1) ^ 3) = x * (x + 1) ^ 3 := by
    rw [one_div, show 2 * x ^ 3 * (x + 1) ^ 3 = (2 * x ^ 2) * (x * (x + 1) ^ 3) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 3) * (2 * x ^ 3 * (x + 1) ^ 3) = (x + 1) ^ 3 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) ^ 3 + 1 / (2 * (x + 1) ^ 2) - 1 / (2 * x ^ 2) =
    -(3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3) := by
  rw [eq_div_iff (by positivity : 2 * x ^ 2 * (x + 1) ^ 3 ≠ 0)]
  have e1 : 1 / (x + 1) ^ 3 * (2 * x ^ 2 * (x + 1) ^ 3) = 2 * x ^ 2 := by
    rw [one_div, show 2 * x ^ 2 * (x + 1) ^ 3 = (x + 1) ^ 3 * (2 * x ^ 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (2 * (x + 1) ^ 2) * (2 * x ^ 2 * (x + 1) ^ 3) = x ^ 2 * (x + 1) := by
    rw [one_div, show 2 * x ^ 2 * (x + 1) ^ 3 = (2 * (x + 1) ^ 2) * (x ^ 2 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * x ^ 2) * (2 * x ^ 2 * (x + 1) ^ 3) = (x + 1) ^ 3 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

/-! ## Step differences -/

lemma ζ_lo_step (N : ℕ) (hN : 1 ≤ N) :
    ζ_lo (N + 1) - ζ_lo N =
      (2 * (N : ℝ) + 1) / (2 * (N : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 3) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) +
      1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2) + 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 3) -
    ((range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) +
      1 / (2 * (N : ℝ) ^ 2) + 1 / (2 * (N : ℝ) ^ 3)) =
    (2 * (N : ℝ) + 1) / (2 * (N : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 3)
  simp only [show (N + 1 : ℕ) - 1 = N from by omega,
    show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) =
      (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) + 1 / (N : ℝ) ^ 3 := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (↑(N - 1) + 1 : ℝ) = (↑N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : ℝ) hN' hN1]

lemma ζ_hi_step (N : ℕ) (hN : 1 ≤ N) :
    ζ_hi (N + 1) - ζ_hi N =
      -(3 * (N : ℝ) + 1) / (2 * (N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 3) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) +
      1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2) -
    ((range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 3) +
      1 / (2 * (N : ℝ) ^ 2)) =
    -(3 * (N : ℝ) + 1) / (2 * (N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 3)
  rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : ℝ) hN' hN1]

/-! ## Monotonicity -/

lemma ζ_lo_step_pos (N : ℕ) (hN : 1 ≤ N) : ζ_lo N < ζ_lo (N + 1) := by
  have h := ζ_lo_step N hN
  have : (0 : ℝ) < (2 * N + 1) / (2 * N ^ 3 * (N + 1) ^ 3) := by
    positivity
  linarith

lemma ζ_hi_step_neg (N : ℕ) (hN : 1 ≤ N) : ζ_hi (N + 1) < ζ_hi N := by
  have h := ζ_hi_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : -(3 * (N : ℝ) + 1) / (2 * N ^ 2 * (N + 1) ^ 3) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

lemma ζ_lo_strictMono : StrictMono (fun N => ζ_lo (N + 1)) :=
  strictMono_nat_of_lt_succ (fun n => ζ_lo_step_pos (n + 1) (by omega))

lemma ζ_hi_strictAnti : StrictAnti (fun N => ζ_hi (N + 1)) :=
  strictAnti_nat_of_succ_lt (fun n => ζ_hi_step_neg (n + 1) (by omega))

/-! ## Convergence -/

private lemma tendsto_correction (p : ℕ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => 1 / (2 * ((N : ℝ) + 1) ^ p)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      ((tendsto_pow_atTop (by omega : p ≠ 0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))

lemma ζ_lo_tendsto :
    Tendsto (fun N => ζ_lo (N + 1)) atTop (𝓝 (riemannZeta 3).re) := by
  unfold ζ_lo
  simp_rw [show ∀ N : ℕ, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 3) +
      (1 / (2 * ((N : ℝ) + 1) ^ 2) + 1 / (2 * ((N : ℝ) + 1) ^ 3)))
      atTop (𝓝 (riemannZeta 3).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 3).re = (riemannZeta 3).re + (0 + 0) from by ring]
  exact tendsto_partial_sum_inv_cube.add
    ((tendsto_correction 2 (by norm_num)).add (tendsto_correction 3 (by norm_num)))

lemma ζ_hi_tendsto :
    Tendsto (fun N => ζ_hi (N + 1)) atTop (𝓝 (riemannZeta 3).re) := by
  unfold ζ_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 3) +
      1 / (2 * ((N : ℝ) + 1) ^ 2))
      atTop (𝓝 (riemannZeta 3).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 3).re = (riemannZeta 3).re + 0 from by ring]
  exact (tendsto_partial_sum_inv_cube.comp (tendsto_add_atTop_nat 1)).add
    (tendsto_correction 2 (by norm_num))

/-! ## Bounds from monotonicity + convergence -/

lemma ζ_lo_le (N : ℕ) (hN : 1 ≤ N) :
    ζ_lo N ≤ (riemannZeta 3).re := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ge_of_tendsto ζ_lo_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ_lo_strictMono.monotone hk⟩)

lemma ζ_hi_ge (N : ℕ) (hN : 1 ≤ N) :
    (riemannZeta 3).re ≤ ζ_hi N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact le_of_tendsto ζ_hi_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ_hi_strictAnti.antitone hk⟩)

/-! ## Computational verification at N = 23 -/

def ζ_lo_q : ℚ :=
  (range 22).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 3) +
    1 / (2 * 23 ^ 2) + 1 / (2 * 23 ^ 3)

def ζ_hi_q : ℚ :=
  (range 23).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 3) +
    1 / (2 * 23 ^ 2)

lemma ζ_lo_q_ge : 12020 / 10000 ≤ ζ_lo_q := by norm_num [ζ_lo_q, Finset.sum_range_succ]
lemma ζ_hi_q_le : ζ_hi_q ≤ 12021 / 10000 := by norm_num [ζ_hi_q, Finset.sum_range_succ]

lemma ζ_lo_q_cast : (ζ_lo_q : ℝ) = ζ_lo 23 := by
  simp only [ζ_lo_q, ζ_lo]; push_cast; norm_num

lemma ζ_hi_q_cast : (ζ_hi_q : ℝ) = ζ_hi 23 := by
  simp only [ζ_hi_q, ζ_hi]; push_cast; norm_num

lemma ζ_lo_23_ge : (12020 : ℝ) / 10000 ≤ ζ_lo 23 := by
  rw [← ζ_lo_q_cast,
    show (12020 : ℝ) / 10000 = ((12020 / 10000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ_lo_q_ge

lemma ζ_hi_23_le : ζ_hi 23 ≤ (12021 : ℝ) / 10000 := by
  rw [← ζ_hi_q_cast,
    show (12021 : ℝ) / 10000 = ((12021 / 10000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ_hi_q_le

end Zeta3Bounds

open Zeta3Bounds in
/-- The real part of the Riemann zeta function at 3 is at least 1.2020. -/
theorem zeta3_lo : (1.2020 : ℝ) ≤ (riemannZeta 3).re :=
  calc (1.2020 : ℝ) = 12020 / 10000 := by norm_num
    _ ≤ ζ_lo 23 := ζ_lo_23_ge
    _ ≤ (riemannZeta 3).re := ζ_lo_le 23 (by norm_num)

open Zeta3Bounds in
/-- The real part of the Riemann zeta function at 3 is at most 1.2021. -/
theorem zeta3_hi : (riemannZeta 3).re ≤ 1.2021 :=
  calc (riemannZeta 3).re ≤ ζ_hi 23 := ζ_hi_ge 23 (by norm_num)
    _ ≤ 12021 / 10000 := ζ_hi_23_le
    _ = 1.2021 := by norm_num
