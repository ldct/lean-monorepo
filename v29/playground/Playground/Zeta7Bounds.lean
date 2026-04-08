import Mathlib


open Real Finset Filter Topology

/-!
# Upper and Lower bounds for ζ(7)

## Key theorems

- `zeta7_lo` : `(100834927 : ℝ) / 100000000 ≤ (riemannZeta 7).re`
- `zeta7_hi` : `(riemannZeta 7).re ≤ (100834928 : ℝ) / 100000000`

## Strategy

Same Euler-Maclaurin approach as Zeta3Bounds/Zeta5Bounds. For f(x) = 1/x⁷:
- ∫_N^∞ 1/x⁷ dx = 1/(6N⁶)
- Midpoint correction: 1/(2N⁷)

Lower sequence S_lo(N) = Σ_{k=1}^{N-1} 1/k⁷ + 1/(6N⁶) + 1/(2N⁷) is increasing.
Upper sequence S_hi(N) = Σ_{k=1}^{N} 1/k⁷ + 1/(6N⁶) is decreasing.
Both converge to ζ(7). At N = 23 we verify the bounds via `norm_num` on ℚ.
-/

namespace Zeta7Bounds

/-! ## Connection to a real-valued tsum -/

lemma summable_inv_seventh_real :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 7) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 7) :=
    (Real.summable_one_div_nat_pow (p := 7)).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 7) 1).mpr h).congr
    (fun n => by congr 1; push_cast; ring)

private lemma summable_inv_seventh_cpow :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (7 : ℂ)) := by
  have hrec : 1 < (7 : ℂ).re := by simp
  rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (7 : ℂ)) =
    (fun n : ℕ => 1 / (n : ℂ) ^ (7 : ℂ)) ∘ (· + 1) from by ext; simp]
  exact (Complex.summable_one_div_nat_cpow.mpr hrec).comp_injective (fun _ _ h => by omega)

lemma zeta7_re_eq_tsum :
    (riemannZeta 7).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 7 := by
  have hrec : 1 < (7 : ℂ).re := by simp
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hrec
  have hterm_re : ∀ n : ℕ, (1 / ((n : ℂ) + 1) ^ (7 : ℂ)).re = 1 / ((n : ℝ) + 1) ^ 7 := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [show ((n : ℂ) + 1) ^ (7 : ℂ) = ((((n : ℝ) + 1) ^ 7 : ℝ) : ℂ) from by
      rw [show (7 : ℂ) = ((7 : ℕ) : ℂ) from by norm_cast, Complex.cpow_natCast]; push_cast; ring]
    rw [show (1 : ℂ) / ((((n : ℝ) + 1) ^ 7 : ℝ) : ℂ) = ((1 / ((n : ℝ) + 1) ^ 7 : ℝ) : ℂ) from by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [hzeta, Complex.re_tsum summable_inv_seventh_cpow]
  congr 1; ext n; exact hterm_re n

lemma tendsto_partial_sum_inv_seventh :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 7)
      atTop (𝓝 (riemannZeta 7).re) := by
  rw [← hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  rw [zeta7_re_eq_tsum]; exact summable_inv_seventh_real.hasSum

/-! ## Define the bounding sequences -/

noncomputable def ζ7_lo (N : ℕ) : ℝ :=
  (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) +
    1 / (6 * (N : ℝ) ^ 6) + 1 / (2 * (N : ℝ) ^ 7)

noncomputable def ζ7_hi (N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) +
    1 / (6 * (N : ℝ) ^ 6)

/-! ## Rational fraction identities

lo step: 1/x⁷ + 1/(6(x+1)⁶) + 1/(2(x+1)⁷) - 1/(6x⁶) - 1/(2x⁷)
       = (2x+1)(14x⁴+28x³+28x²+14x+3) / (6x⁷(x+1)⁷)

hi step: 1/(x+1)⁷ + 1/(6(x+1)⁶) - 1/(6x⁶)
       = -(21x⁵+35x⁴+35x³+21x²+7x+1) / (6x⁶(x+1)⁷)
-/

private lemma lo_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x ^ 7 + 1 / (6 * (x + 1) ^ 6) + 1 / (2 * (x + 1) ^ 7) -
    1 / (6 * x ^ 6) - 1 / (2 * x ^ 7) =
    (2 * x + 1) * (14 * x ^ 4 + 28 * x ^ 3 + 28 * x ^ 2 + 14 * x + 3) /
      (6 * x ^ 7 * (x + 1) ^ 7) := by
  rw [eq_div_iff (by positivity : 6 * x ^ 7 * (x + 1) ^ 7 ≠ 0)]
  have e1 : 1 / x ^ 7 * (6 * x ^ 7 * (x + 1) ^ 7) = 6 * (x + 1) ^ 7 := by
    rw [one_div, show 6 * x ^ 7 * (x + 1) ^ 7 = x ^ 7 * (6 * (x + 1) ^ 7) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (6 * (x + 1) ^ 6) * (6 * x ^ 7 * (x + 1) ^ 7) = x ^ 7 * (x + 1) := by
    rw [one_div, show 6 * x ^ 7 * (x + 1) ^ 7 = (6 * (x + 1) ^ 6) * (x ^ 7 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ 7) * (6 * x ^ 7 * (x + 1) ^ 7) = 3 * x ^ 7 := by
    rw [one_div, show 6 * x ^ 7 * (x + 1) ^ 7 = (2 * (x + 1) ^ 7) * (3 * x ^ 7) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / (6 * x ^ 6) * (6 * x ^ 7 * (x + 1) ^ 7) = x * (x + 1) ^ 7 := by
    rw [one_div, show 6 * x ^ 7 * (x + 1) ^ 7 = (6 * x ^ 6) * (x * (x + 1) ^ 7) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 7) * (6 * x ^ 7 * (x + 1) ^ 7) = 3 * (x + 1) ^ 7 := by
    rw [one_div, show 6 * x ^ 7 * (x + 1) ^ 7 = (2 * x ^ 7) * (3 * (x + 1) ^ 7) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) ^ 7 + 1 / (6 * (x + 1) ^ 6) - 1 / (6 * x ^ 6) =
    -(21 * x ^ 5 + 35 * x ^ 4 + 35 * x ^ 3 + 21 * x ^ 2 + 7 * x + 1) /
      (6 * x ^ 6 * (x + 1) ^ 7) := by
  rw [eq_div_iff (by positivity : 6 * x ^ 6 * (x + 1) ^ 7 ≠ 0)]
  have e1 : 1 / (x + 1) ^ 7 * (6 * x ^ 6 * (x + 1) ^ 7) = 6 * x ^ 6 := by
    rw [one_div, show 6 * x ^ 6 * (x + 1) ^ 7 = (x + 1) ^ 7 * (6 * x ^ 6) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (6 * (x + 1) ^ 6) * (6 * x ^ 6 * (x + 1) ^ 7) = x ^ 6 * (x + 1) := by
    rw [one_div, show 6 * x ^ 6 * (x + 1) ^ 7 = (6 * (x + 1) ^ 6) * (x ^ 6 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (6 * x ^ 6) * (6 * x ^ 6 * (x + 1) ^ 7) = (x + 1) ^ 7 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

/-! ## Step differences -/

lemma ζ7_lo_step (N : ℕ) (hN : 1 ≤ N) :
    ζ7_lo (N + 1) - ζ7_lo N =
      (2 * (N : ℝ) + 1) * (14 * (N : ℝ) ^ 4 + 28 * (N : ℝ) ^ 3 + 28 * (N : ℝ) ^ 2 +
        14 * (N : ℝ) + 3) /
        (6 * (N : ℝ) ^ 7 * ((N : ℝ) + 1) ^ 7) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) +
      1 / (6 * ((N + 1 : ℕ) : ℝ) ^ 6) + 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 7) -
    ((range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) +
      1 / (6 * (N : ℝ) ^ 6) + 1 / (2 * (N : ℝ) ^ 7)) =
    (2 * (N : ℝ) + 1) * (14 * (N : ℝ) ^ 4 + 28 * (N : ℝ) ^ 3 + 28 * (N : ℝ) ^ 2 +
      14 * (N : ℝ) + 3) /
      (6 * (N : ℝ) ^ 7 * ((N : ℝ) + 1) ^ 7)
  simp only [show (N + 1 : ℕ) - 1 = N from by omega,
    show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) =
      (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) + 1 / (N : ℝ) ^ 7 := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (↑(N - 1) + 1 : ℝ) = (↑N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : ℝ) hN' hN1]

lemma ζ7_hi_step (N : ℕ) (hN : 1 ≤ N) :
    ζ7_hi (N + 1) - ζ7_hi N =
      -(21 * (N : ℝ) ^ 5 + 35 * (N : ℝ) ^ 4 + 35 * (N : ℝ) ^ 3 +
        21 * (N : ℝ) ^ 2 + 7 * (N : ℝ) + 1) /
        (6 * (N : ℝ) ^ 6 * ((N : ℝ) + 1) ^ 7) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) +
      1 / (6 * ((N + 1 : ℕ) : ℝ) ^ 6) -
    ((range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 7) +
      1 / (6 * (N : ℝ) ^ 6)) =
    -(21 * (N : ℝ) ^ 5 + 35 * (N : ℝ) ^ 4 + 35 * (N : ℝ) ^ 3 +
      21 * (N : ℝ) ^ 2 + 7 * (N : ℝ) + 1) /
      (6 * (N : ℝ) ^ 6 * ((N : ℝ) + 1) ^ 7)
  rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : ℝ) hN' hN1]

/-! ## Monotonicity -/

lemma ζ7_lo_step_pos (N : ℕ) (hN : 1 ≤ N) : ζ7_lo N < ζ7_lo (N + 1) := by
  have h := ζ7_lo_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : (0 : ℝ) < (2 * N + 1) * (14 * N ^ 4 + 28 * N ^ 3 + 28 * N ^ 2 +
      14 * N + 3) / (6 * N ^ 7 * (N + 1) ^ 7) := by positivity
  linarith

lemma ζ7_hi_step_neg (N : ℕ) (hN : 1 ≤ N) : ζ7_hi (N + 1) < ζ7_hi N := by
  have h := ζ7_hi_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hnum : 21 * (N : ℝ) ^ 5 + 35 * (N : ℝ) ^ 4 + 35 * (N : ℝ) ^ 3 +
      21 * (N : ℝ) ^ 2 + 7 * (N : ℝ) + 1 > 0 := by positivity
  have : -(21 * (N : ℝ) ^ 5 + 35 * (N : ℝ) ^ 4 + 35 * (N : ℝ) ^ 3 +
      21 * (N : ℝ) ^ 2 + 7 * (N : ℝ) + 1) /
      (6 * (N : ℝ) ^ 6 * ((N : ℝ) + 1) ^ 7) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

lemma ζ7_lo_strictMono : StrictMono (fun N => ζ7_lo (N + 1)) :=
  strictMono_nat_of_lt_succ (fun n => ζ7_lo_step_pos (n + 1) (by omega))

lemma ζ7_hi_strictAnti : StrictAnti (fun N => ζ7_hi (N + 1)) :=
  strictAnti_nat_of_succ_lt (fun n => ζ7_hi_step_neg (n + 1) (by omega))

/-! ## Convergence -/

private lemma tendsto_correction (c : ℝ) (hc : 0 < c) (p : ℕ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => 1 / (c * ((N : ℝ) + 1) ^ p)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Tendsto.const_mul_atTop hc
      ((tendsto_pow_atTop (by omega : p ≠ 0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))

lemma ζ7_lo_tendsto :
    Tendsto (fun N => ζ7_lo (N + 1)) atTop (𝓝 (riemannZeta 7).re) := by
  unfold ζ7_lo
  simp_rw [show ∀ N : ℕ, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 7) +
      (1 / (6 * ((N : ℝ) + 1) ^ 6) + 1 / (2 * ((N : ℝ) + 1) ^ 7)))
      atTop (𝓝 (riemannZeta 7).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 7).re = (riemannZeta 7).re + (0 + 0) from by ring]
  exact tendsto_partial_sum_inv_seventh.add
    ((tendsto_correction 6 (by norm_num) 6 (by norm_num)).add
      (tendsto_correction 2 (by norm_num) 7 (by norm_num)))

lemma ζ7_hi_tendsto :
    Tendsto (fun N => ζ7_hi (N + 1)) atTop (𝓝 (riemannZeta 7).re) := by
  unfold ζ7_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 7) +
      1 / (6 * ((N : ℝ) + 1) ^ 6))
      atTop (𝓝 (riemannZeta 7).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 7).re = (riemannZeta 7).re + 0 from by ring]
  exact (tendsto_partial_sum_inv_seventh.comp (tendsto_add_atTop_nat 1)).add
    (tendsto_correction 6 (by norm_num) 6 (by norm_num))

/-! ## Bounds from monotonicity + convergence -/

lemma ζ7_lo_le (N : ℕ) (hN : 1 ≤ N) :
    ζ7_lo N ≤ (riemannZeta 7).re := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ge_of_tendsto ζ7_lo_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ7_lo_strictMono.monotone hk⟩)

lemma ζ7_hi_ge (N : ℕ) (hN : 1 ≤ N) :
    (riemannZeta 7).re ≤ ζ7_hi N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact le_of_tendsto ζ7_hi_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ7_hi_strictAnti.antitone hk⟩)

/-! ## Computational verification at N = 23 -/

def ζ7_lo_q : ℚ :=
  (range 22).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 7) +
    1 / (6 * 23 ^ 6) + 1 / (2 * 23 ^ 7)

def ζ7_hi_q : ℚ :=
  (range 23).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 7) +
    1 / (6 * 23 ^ 6)

set_option maxHeartbeats 4000000 in
lemma ζ7_lo_q_ge : 100834927 / 100000000 ≤ ζ7_lo_q := by norm_num [ζ7_lo_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma ζ7_hi_q_le : ζ7_hi_q ≤ 100834928 / 100000000 := by norm_num [ζ7_hi_q, Finset.sum_range_succ]

lemma ζ7_lo_q_cast : (ζ7_lo_q : ℝ) = ζ7_lo 23 := by
  simp only [ζ7_lo_q, ζ7_lo]; push_cast; norm_num

lemma ζ7_hi_q_cast : (ζ7_hi_q : ℝ) = ζ7_hi 23 := by
  simp only [ζ7_hi_q, ζ7_hi]; push_cast; norm_num

lemma ζ7_lo_23_ge : (100834927 : ℝ) / 100000000 ≤ ζ7_lo 23 := by
  rw [← ζ7_lo_q_cast,
    show (100834927 : ℝ) / 100000000 = ((100834927 / 100000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ7_lo_q_ge

lemma ζ7_hi_23_le : ζ7_hi 23 ≤ (100834928 : ℝ) / 100000000 := by
  rw [← ζ7_hi_q_cast,
    show (100834928 : ℝ) / 100000000 = ((100834928 / 100000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ7_hi_q_le

end Zeta7Bounds

open Zeta7Bounds in
/-- The real part of the Riemann zeta function at 7 is at least 100834927/100000000. -/
theorem zeta7_lo : (100834927 : ℝ) / 100000000 ≤ (riemannZeta 7).re :=
  calc (100834927 : ℝ) / 100000000
      _ ≤ ζ7_lo 23 := ζ7_lo_23_ge
      _ ≤ (riemannZeta 7).re := ζ7_lo_le 23 (by norm_num)

open Zeta7Bounds in
/-- The real part of the Riemann zeta function at 7 is at most 100834928/100000000. -/
theorem zeta7_hi : (riemannZeta 7).re ≤ (100834928 : ℝ) / 100000000 :=
  calc (riemannZeta 7).re ≤ ζ7_hi 23 := ζ7_hi_ge 23 (by norm_num)
    _ ≤ 100834928 / 100000000 := ζ7_hi_23_le
