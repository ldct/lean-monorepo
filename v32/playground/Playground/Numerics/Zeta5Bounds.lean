import Mathlib


open Real Finset Filter Topology

/-!
# Upper and Lower bounds for ζ(5)

## Key theorems

- `zeta5_lo` : `(103692 : ℝ) / 100000 ≤ (riemannZeta 5).re`
- `zeta5_hi` : `(riemannZeta 5).re ≤ (103693 : ℝ) / 100000`

## Strategy

Same Euler-Maclaurin approach as Zeta3Bounds. For f(x) = 1/x⁵:
- ∫_N^∞ 1/x⁵ dx = 1/(4N⁴)
- Midpoint correction: 1/(2N⁵)

Lower sequence S_lo(N) = Σ_{k=1}^{N-1} 1/k⁵ + 1/(4N⁴) + 1/(2N⁵) is increasing.
Upper sequence S_hi(N) = Σ_{k=1}^{N} 1/k⁵ + 1/(4N⁴) is decreasing.
Both converge to ζ(5). At N = 23 we verify the bounds via `norm_num` on ℚ.
-/

namespace Zeta5Bounds

/-! ## Connection to a real-valued tsum -/

lemma summable_inv_fifth_real :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 5) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 5) :=
    (Real.summable_one_div_nat_pow (p := 5)).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 5) 1).mpr h).congr
    (fun n => by congr 1; push_cast; ring)

private lemma summable_inv_fifth_cpow :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (5 : ℂ)) := by
  have hrec : 1 < (5 : ℂ).re := by simp
  rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (5 : ℂ)) =
    (fun n : ℕ => 1 / (n : ℂ) ^ (5 : ℂ)) ∘ (· + 1) from by ext; simp]
  exact (Complex.summable_one_div_nat_cpow.mpr hrec).comp_injective (fun _ _ h => by omega)

lemma zeta5_re_eq_tsum :
    (riemannZeta 5).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5 := by
  have hrec : 1 < (5 : ℂ).re := by simp
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hrec
  have hterm_re : ∀ n : ℕ, (1 / ((n : ℂ) + 1) ^ (5 : ℂ)).re = 1 / ((n : ℝ) + 1) ^ 5 := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [show ((n : ℂ) + 1) ^ (5 : ℂ) = ((((n : ℝ) + 1) ^ 5 : ℝ) : ℂ) from by
      rw [show (5 : ℂ) = ((5 : ℕ) : ℂ) from by norm_cast, Complex.cpow_natCast]; push_cast; ring]
    rw [show (1 : ℂ) / ((((n : ℝ) + 1) ^ 5 : ℝ) : ℂ) = ((1 / ((n : ℝ) + 1) ^ 5 : ℝ) : ℂ) from by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [hzeta, Complex.re_tsum summable_inv_fifth_cpow]
  congr 1; ext n; exact hterm_re n

lemma tendsto_partial_sum_inv_fifth :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 5)
      atTop (𝓝 (riemannZeta 5).re) := by
  rw [← hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  rw [zeta5_re_eq_tsum]; exact summable_inv_fifth_real.hasSum

/-! ## Define the bounding sequences -/

noncomputable def ζ5_lo (N : ℕ) : ℝ :=
  (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) +
    1 / (4 * (N : ℝ) ^ 4) + 1 / (2 * (N : ℝ) ^ 5)

noncomputable def ζ5_hi (N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) +
    1 / (4 * (N : ℝ) ^ 4)

/-! ## Rational fraction identities -/

private lemma lo_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x ^ 5 + 1 / (4 * (x + 1) ^ 4) + 1 / (2 * (x + 1) ^ 5) -
    1 / (4 * x ^ 4) - 1 / (2 * x ^ 5) =
    (2 * x + 1) * (5 * x ^ 2 + 5 * x + 2) / (4 * x ^ 5 * (x + 1) ^ 5) := by
  rw [eq_div_iff (by positivity : 4 * x ^ 5 * (x + 1) ^ 5 ≠ 0)]
  have e1 : 1 / x ^ 5 * (4 * x ^ 5 * (x + 1) ^ 5) = 4 * (x + 1) ^ 5 := by
    rw [one_div, show 4 * x ^ 5 * (x + 1) ^ 5 = x ^ 5 * (4 * (x + 1) ^ 5) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (4 * (x + 1) ^ 4) * (4 * x ^ 5 * (x + 1) ^ 5) = x ^ 5 * (x + 1) := by
    rw [one_div, show 4 * x ^ 5 * (x + 1) ^ 5 = (4 * (x + 1) ^ 4) * (x ^ 5 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ 5) * (4 * x ^ 5 * (x + 1) ^ 5) = 2 * x ^ 5 := by
    rw [one_div, show 4 * x ^ 5 * (x + 1) ^ 5 = (2 * (x + 1) ^ 5) * (2 * x ^ 5) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / (4 * x ^ 4) * (4 * x ^ 5 * (x + 1) ^ 5) = x * (x + 1) ^ 5 := by
    rw [one_div, show 4 * x ^ 5 * (x + 1) ^ 5 = (4 * x ^ 4) * (x * (x + 1) ^ 5) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 5) * (4 * x ^ 5 * (x + 1) ^ 5) = 2 * (x + 1) ^ 5 := by
    rw [one_div, show 4 * x ^ 5 * (x + 1) ^ 5 = (2 * x ^ 5) * (2 * (x + 1) ^ 5) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) ^ 5 + 1 / (4 * (x + 1) ^ 4) - 1 / (4 * x ^ 4) =
    -(10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1) / (4 * x ^ 4 * (x + 1) ^ 5) := by
  rw [eq_div_iff (by positivity : 4 * x ^ 4 * (x + 1) ^ 5 ≠ 0)]
  have e1 : 1 / (x + 1) ^ 5 * (4 * x ^ 4 * (x + 1) ^ 5) = 4 * x ^ 4 := by
    rw [one_div, show 4 * x ^ 4 * (x + 1) ^ 5 = (x + 1) ^ 5 * (4 * x ^ 4) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (4 * (x + 1) ^ 4) * (4 * x ^ 4 * (x + 1) ^ 5) = x ^ 4 * (x + 1) := by
    rw [one_div, show 4 * x ^ 4 * (x + 1) ^ 5 = (4 * (x + 1) ^ 4) * (x ^ 4 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (4 * x ^ 4) * (4 * x ^ 4 * (x + 1) ^ 5) = (x + 1) ^ 5 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

/-! ## Step differences -/

lemma ζ5_lo_step (N : ℕ) (hN : 1 ≤ N) :
    ζ5_lo (N + 1) - ζ5_lo N =
      (2 * (N : ℝ) + 1) * (5 * (N : ℝ) ^ 2 + 5 * (N : ℝ) + 2) /
        (4 * (N : ℝ) ^ 5 * ((N : ℝ) + 1) ^ 5) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) +
      1 / (4 * ((N + 1 : ℕ) : ℝ) ^ 4) + 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 5) -
    ((range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) +
      1 / (4 * (N : ℝ) ^ 4) + 1 / (2 * (N : ℝ) ^ 5)) =
    (2 * (N : ℝ) + 1) * (5 * (N : ℝ) ^ 2 + 5 * (N : ℝ) + 2) /
      (4 * (N : ℝ) ^ 5 * ((N : ℝ) + 1) ^ 5)
  simp only [show (N + 1 : ℕ) - 1 = N from by omega,
    show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) =
      (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) + 1 / (N : ℝ) ^ 5 := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (↑(N - 1) + 1 : ℝ) = (↑N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : ℝ) hN' hN1]

lemma ζ5_hi_step (N : ℕ) (hN : 1 ≤ N) :
    ζ5_hi (N + 1) - ζ5_hi N =
      -(10 * (N : ℝ) ^ 3 + 10 * (N : ℝ) ^ 2 + 5 * (N : ℝ) + 1) /
        (4 * (N : ℝ) ^ 4 * ((N : ℝ) + 1) ^ 5) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) +
      1 / (4 * ((N + 1 : ℕ) : ℝ) ^ 4) -
    ((range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 5) +
      1 / (4 * (N : ℝ) ^ 4)) =
    -(10 * (N : ℝ) ^ 3 + 10 * (N : ℝ) ^ 2 + 5 * (N : ℝ) + 1) /
      (4 * (N : ℝ) ^ 4 * ((N : ℝ) + 1) ^ 5)
  rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : ℝ) hN' hN1]

/-! ## Monotonicity -/

lemma ζ5_lo_step_pos (N : ℕ) (hN : 1 ≤ N) : ζ5_lo N < ζ5_lo (N + 1) := by
  have h := ζ5_lo_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : (0 : ℝ) < (2 * N + 1) * (5 * N ^ 2 + 5 * N + 2) /
      (4 * N ^ 5 * (N + 1) ^ 5) := by positivity
  linarith

lemma ζ5_hi_step_neg (N : ℕ) (hN : 1 ≤ N) : ζ5_hi (N + 1) < ζ5_hi N := by
  have h := ζ5_hi_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : -(10 * (N : ℝ) ^ 3 + 10 * (N : ℝ) ^ 2 + 5 * (N : ℝ) + 1) /
      (4 * (N : ℝ) ^ 4 * ((N : ℝ) + 1) ^ 5) < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith

lemma ζ5_lo_strictMono : StrictMono (fun N => ζ5_lo (N + 1)) :=
  strictMono_nat_of_lt_succ (fun n => ζ5_lo_step_pos (n + 1) (by omega))

lemma ζ5_hi_strictAnti : StrictAnti (fun N => ζ5_hi (N + 1)) :=
  strictAnti_nat_of_succ_lt (fun n => ζ5_hi_step_neg (n + 1) (by omega))

/-! ## Convergence -/

private lemma tendsto_correction (p : ℕ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => 1 / (2 * ((N : ℝ) + 1) ^ p)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      ((tendsto_pow_atTop (by omega : p ≠ 0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))

private lemma tendsto_correction' (p : ℕ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => 1 / (4 * ((N : ℝ) + 1) ^ p)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
      ((tendsto_pow_atTop (by omega : p ≠ 0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))

lemma ζ5_lo_tendsto :
    Tendsto (fun N => ζ5_lo (N + 1)) atTop (𝓝 (riemannZeta 5).re) := by
  unfold ζ5_lo
  simp_rw [show ∀ N : ℕ, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 5) +
      (1 / (4 * ((N : ℝ) + 1) ^ 4) + 1 / (2 * ((N : ℝ) + 1) ^ 5)))
      atTop (𝓝 (riemannZeta 5).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 5).re = (riemannZeta 5).re + (0 + 0) from by ring]
  exact tendsto_partial_sum_inv_fifth.add
    ((tendsto_correction' 4 (by norm_num)).add (tendsto_correction 5 (by norm_num)))

lemma ζ5_hi_tendsto :
    Tendsto (fun N => ζ5_hi (N + 1)) atTop (𝓝 (riemannZeta 5).re) := by
  unfold ζ5_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 5) +
      1 / (4 * ((N : ℝ) + 1) ^ 4))
      atTop (𝓝 (riemannZeta 5).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 5).re = (riemannZeta 5).re + 0 from by ring]
  exact (tendsto_partial_sum_inv_fifth.comp (tendsto_add_atTop_nat 1)).add
    (tendsto_correction' 4 (by norm_num))

/-! ## Bounds from monotonicity + convergence -/

lemma ζ5_lo_le (N : ℕ) (hN : 1 ≤ N) :
    ζ5_lo N ≤ (riemannZeta 5).re := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ge_of_tendsto ζ5_lo_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ5_lo_strictMono.monotone hk⟩)

lemma ζ5_hi_ge (N : ℕ) (hN : 1 ≤ N) :
    (riemannZeta 5).re ≤ ζ5_hi N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact le_of_tendsto ζ5_hi_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ5_hi_strictAnti.antitone hk⟩)

/-! ## Computational verification at N = 23 -/

def ζ5_lo_q : ℚ :=
  (range 22).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 5) +
    1 / (4 * 23 ^ 4) + 1 / (2 * 23 ^ 5)

def ζ5_hi_q : ℚ :=
  (range 23).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 5) +
    1 / (4 * 23 ^ 4)

set_option maxHeartbeats 4000000 in
lemma ζ5_lo_q_ge : 103692 / 100000 ≤ ζ5_lo_q := by norm_num [ζ5_lo_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma ζ5_hi_q_le : ζ5_hi_q ≤ 103693 / 100000 := by norm_num [ζ5_hi_q, Finset.sum_range_succ]

lemma ζ5_lo_q_cast : (ζ5_lo_q : ℝ) = ζ5_lo 23 := by
  simp only [ζ5_lo_q, ζ5_lo]; push_cast; norm_num

lemma ζ5_hi_q_cast : (ζ5_hi_q : ℝ) = ζ5_hi 23 := by
  simp only [ζ5_hi_q, ζ5_hi]; push_cast; norm_num

lemma ζ5_lo_23_ge : (103692 : ℝ) / 100000 ≤ ζ5_lo 23 := by
  rw [← ζ5_lo_q_cast,
    show (103692 : ℝ) / 100000 = ((103692 / 100000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ5_lo_q_ge

lemma ζ5_hi_23_le : ζ5_hi 23 ≤ (103693 : ℝ) / 100000 := by
  rw [← ζ5_hi_q_cast,
    show (103693 : ℝ) / 100000 = ((103693 / 100000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ5_hi_q_le

end Zeta5Bounds

open Zeta5Bounds in
/-- The real part of the Riemann zeta function at 5 is at least 103692/100000. -/
theorem zeta5_lo : (103692 : ℝ) / 100000 ≤ (riemannZeta 5).re :=
  calc (103692 : ℝ) / 100000
      _ ≤ ζ5_lo 23 := ζ5_lo_23_ge
      _ ≤ (riemannZeta 5).re := ζ5_lo_le 23 (by norm_num)

open Zeta5Bounds in
/-- The real part of the Riemann zeta function at 5 is at most 103693/100000. -/
theorem zeta5_hi : (riemannZeta 5).re ≤ (103693 : ℝ) / 100000 :=
  calc (riemannZeta 5).re ≤ ζ5_hi 23 := ζ5_hi_ge 23 (by norm_num)
    _ ≤ 103693 / 100000 := ζ5_hi_23_le
