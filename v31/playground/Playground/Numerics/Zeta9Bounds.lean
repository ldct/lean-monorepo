import Mathlib


open Real Finset Filter Topology

/-!
# Upper and Lower bounds for ζ(9)

## Key theorems

- `zeta9_lo` : `(10020083928 : ℝ) / 10000000000 ≤ (riemannZeta 9).re`
- `zeta9_hi` : `(riemannZeta 9).re ≤ (10020083929 : ℝ) / 10000000000`

Same Euler-Maclaurin approach as Zeta3Bounds. N = 23 gives 10 decimal places.
-/

namespace Zeta9Bounds

lemma summable_real :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 9) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 9) :=
    (Real.summable_one_div_nat_pow (p := 9)).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 9) 1).mpr h).congr
    (fun n => by congr 1; push_cast; ring)

private lemma summable_cpow :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (9 : ℂ)) := by
  have hrec : 1 < (9 : ℂ).re := by simp
  rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (9 : ℂ)) =
    (fun n : ℕ => 1 / (n : ℂ) ^ (9 : ℂ)) ∘ (· + 1) from by ext; simp]
  exact (Complex.summable_one_div_nat_cpow.mpr hrec).comp_injective (fun _ _ h => by omega)

lemma re_eq_tsum :
    (riemannZeta 9).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 9 := by
  have hrec : 1 < (9 : ℂ).re := by simp
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hrec
  have hterm_re : ∀ n : ℕ, (1 / ((n : ℂ) + 1) ^ (9 : ℂ)).re = 1 / ((n : ℝ) + 1) ^ 9 := by
    intro n
    rw [show ((n : ℂ) + 1) ^ (9 : ℂ) = ((((n : ℝ) + 1) ^ 9 : ℝ) : ℂ) from by
      rw [show (9 : ℂ) = ((9 : ℕ) : ℂ) from by norm_cast, Complex.cpow_natCast]; push_cast; ring]
    rw [show (1 : ℂ) / ((((n : ℝ) + 1) ^ 9 : ℝ) : ℂ) = ((1 / ((n : ℝ) + 1) ^ 9 : ℝ) : ℂ) from by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [hzeta, Complex.re_tsum summable_cpow]
  congr 1; ext n; exact hterm_re n

lemma tendsto_partial_sum :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 9)
      atTop (𝓝 (riemannZeta 9).re) := by
  rw [← hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  rw [re_eq_tsum]; exact summable_real.hasSum

noncomputable def S_lo (N : ℕ) : ℝ :=
  (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) +
    1 / (8 * (N : ℝ) ^ 8) + 1 / (2 * (N : ℝ) ^ 9)

noncomputable def S_hi (N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) +
    1 / (8 * (N : ℝ) ^ 8)

private lemma lo_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x ^ 9 + 1 / (8 * (x + 1) ^ 8) + 1 / (2 * (x + 1) ^ 9) -
    1 / (8 * x ^ 8) - 1 / (2 * x ^ 9) =
    (2 * x + 1) * (4 + 27 * x + 81 * x ^ 2 + 138 * x ^ 3 + 144 * x ^ 4 + 90 * x ^ 5 + 30 * x ^ 6) /
      (8 * x ^ 9 * (x + 1) ^ 9) := by
  rw [eq_div_iff (by positivity : (8 : ℝ) * x ^ 9 * (x + 1) ^ 9 ≠ 0)]
  have e1 : 1 / x ^ 9 * (8 * x ^ 9 * (x + 1) ^ 9) = 8 * (x + 1) ^ 9 := by
    rw [one_div, show 8 * x ^ 9 * (x + 1) ^ 9 = x ^ 9 * (8 * (x + 1) ^ 9) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (8 * (x + 1) ^ 8) * (8 * x ^ 9 * (x + 1) ^ 9) = x ^ 9 * (x + 1) := by
    rw [one_div, show 8 * x ^ 9 * (x + 1) ^ 9 = (8 * (x + 1) ^ 8) * (x ^ 9 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ 9) * (8 * x ^ 9 * (x + 1) ^ 9) = 8 * x ^ 9 / 2 := by
    rw [one_div, show 8 * x ^ 9 * (x + 1) ^ 9 = (2 * (x + 1) ^ 9) * (8 * x ^ 9 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / (8 * x ^ 8) * (8 * x ^ 9 * (x + 1) ^ 9) = x * (x + 1) ^ 9 := by
    rw [one_div, show 8 * x ^ 9 * (x + 1) ^ 9 = (8 * x ^ 8) * (x * (x + 1) ^ 9) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 9) * (8 * x ^ 9 * (x + 1) ^ 9) = 8 * (x + 1) ^ 9 / 2 := by
    rw [one_div, show 8 * x ^ 9 * (x + 1) ^ 9 = (2 * x ^ 9) * (8 * (x + 1) ^ 9 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) ^ 9 + 1 / (8 * (x + 1) ^ 8) - 1 / (8 * x ^ 8) =
    -(1 + 9 * x + 36 * x ^ 2 + 84 * x ^ 3 + 126 * x ^ 4 + 126 * x ^ 5 + 84 * x ^ 6 + 36 * x ^ 7) /
      (8 * x ^ 8 * (x + 1) ^ 9) := by
  rw [eq_div_iff (by positivity : (8 : ℝ) * x ^ 8 * (x + 1) ^ 9 ≠ 0)]
  have e1 : 1 / (x + 1) ^ 9 * (8 * x ^ 8 * (x + 1) ^ 9) = 8 * x ^ 8 := by
    rw [one_div, show 8 * x ^ 8 * (x + 1) ^ 9 = (x + 1) ^ 9 * (8 * x ^ 8) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (8 * (x + 1) ^ 8) * (8 * x ^ 8 * (x + 1) ^ 9) = x ^ 8 * (x + 1) := by
    rw [one_div, show 8 * x ^ 8 * (x + 1) ^ 9 = (8 * (x + 1) ^ 8) * (x ^ 8 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (8 * x ^ 8) * (8 * x ^ 8 * (x + 1) ^ 9) = (x + 1) ^ 9 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

lemma S_lo_step (N : ℕ) (hN : 1 ≤ N) :
    S_lo (N + 1) - S_lo N =
      (2 * (N : ℝ) + 1) * (4 + 27 * (N : ℝ) + 81 * (N : ℝ) ^ 2 + 138 * (N : ℝ) ^ 3 + 144 * (N : ℝ) ^ 4 + 90 * (N : ℝ) ^ 5 + 30 * (N : ℝ) ^ 6) /
        (8 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) ^ 9) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) +
      1 / (8 * ((N + 1 : ℕ) : ℝ) ^ 8) + 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 9) -
    ((range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) +
      1 / (8 * (N : ℝ) ^ 8) + 1 / (2 * (N : ℝ) ^ 9)) =
    (2 * (N : ℝ) + 1) * (4 + 27 * (N : ℝ) + 81 * (N : ℝ) ^ 2 + 138 * (N : ℝ) ^ 3 + 144 * (N : ℝ) ^ 4 + 90 * (N : ℝ) ^ 5 + 30 * (N : ℝ) ^ 6) /
      (8 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) ^ 9)
  simp only [show (N + 1 : ℕ) - 1 = N from by omega,
    show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) =
      (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) + 1 / (N : ℝ) ^ 9 := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (↑(N - 1) + 1 : ℝ) = (↑N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : ℝ) hN' hN1]

lemma S_hi_step (N : ℕ) (hN : 1 ≤ N) :
    S_hi (N + 1) - S_hi N =
      -(1 + 9 * (N : ℝ) + 36 * (N : ℝ) ^ 2 + 84 * (N : ℝ) ^ 3 + 126 * (N : ℝ) ^ 4 + 126 * (N : ℝ) ^ 5 + 84 * (N : ℝ) ^ 6 + 36 * (N : ℝ) ^ 7) /
        (8 * (N : ℝ) ^ 8 * ((N : ℝ) + 1) ^ 9) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) +
      1 / (8 * ((N + 1 : ℕ) : ℝ) ^ 8) -
    ((range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 9) +
      1 / (8 * (N : ℝ) ^ 8)) =
    -(1 + 9 * (N : ℝ) + 36 * (N : ℝ) ^ 2 + 84 * (N : ℝ) ^ 3 + 126 * (N : ℝ) ^ 4 + 126 * (N : ℝ) ^ 5 + 84 * (N : ℝ) ^ 6 + 36 * (N : ℝ) ^ 7) /
      (8 * (N : ℝ) ^ 8 * ((N : ℝ) + 1) ^ 9)
  rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : ℝ) hN' hN1]

lemma S_lo_step_pos (N : ℕ) (hN : 1 ≤ N) : S_lo N < S_lo (N + 1) := by
  have h := S_lo_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : (0 : ℝ) < (2 * N + 1) * (4 + 27 * (N : ℝ) + 81 * (N : ℝ) ^ 2 + 138 * (N : ℝ) ^ 3 + 144 * (N : ℝ) ^ 4 + 90 * (N : ℝ) ^ 5 + 30 * (N : ℝ) ^ 6) /
      (8 * N ^ 9 * (N + 1) ^ 9) := by positivity
  linarith

lemma S_hi_step_neg (N : ℕ) (hN : 1 ≤ N) : S_hi (N + 1) < S_hi N := by
  have h := S_hi_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hnum : (1 + 9 * (N : ℝ) + 36 * (N : ℝ) ^ 2 + 84 * (N : ℝ) ^ 3 + 126 * (N : ℝ) ^ 4 + 126 * (N : ℝ) ^ 5 + 84 * (N : ℝ) ^ 6 + 36 * (N : ℝ) ^ 7) > 0 := by positivity
  have : -(1 + 9 * (N : ℝ) + 36 * (N : ℝ) ^ 2 + 84 * (N : ℝ) ^ 3 + 126 * (N : ℝ) ^ 4 + 126 * (N : ℝ) ^ 5 + 84 * (N : ℝ) ^ 6 + 36 * (N : ℝ) ^ 7) /
      (8 * (N : ℝ) ^ 8 * ((N : ℝ) + 1) ^ 9) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

lemma S_lo_strictMono : StrictMono (fun N => S_lo (N + 1)) :=
  strictMono_nat_of_lt_succ (fun n => S_lo_step_pos (n + 1) (by omega))

lemma S_hi_strictAnti : StrictAnti (fun N => S_hi (N + 1)) :=
  strictAnti_nat_of_succ_lt (fun n => S_hi_step_neg (n + 1) (by omega))

private lemma tendsto_correction (c : ℝ) (hc : 0 < c) (p : ℕ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => 1 / (c * ((N : ℝ) + 1) ^ p)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Tendsto.const_mul_atTop hc
      ((tendsto_pow_atTop (by omega : p ≠ 0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))

lemma S_lo_tendsto :
    Tendsto (fun N => S_lo (N + 1)) atTop (𝓝 (riemannZeta 9).re) := by
  unfold S_lo
  simp_rw [show ∀ N : ℕ, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 9) +
      (1 / (8 * ((N : ℝ) + 1) ^ 8) + 1 / (2 * ((N : ℝ) + 1) ^ 9)))
      atTop (𝓝 (riemannZeta 9).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 9).re = (riemannZeta 9).re + (0 + 0) from by ring]
  exact tendsto_partial_sum.add
    ((tendsto_correction 8 (by norm_num) 8 (by norm_num)).add
      (tendsto_correction 2 (by norm_num) 9 (by norm_num)))

lemma S_hi_tendsto :
    Tendsto (fun N => S_hi (N + 1)) atTop (𝓝 (riemannZeta 9).re) := by
  unfold S_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 9) +
      1 / (8 * ((N : ℝ) + 1) ^ 8))
      atTop (𝓝 (riemannZeta 9).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 9).re = (riemannZeta 9).re + 0 from by ring]
  exact (tendsto_partial_sum.comp (tendsto_add_atTop_nat 1)).add
    (tendsto_correction 8 (by norm_num) 8 (by norm_num))

lemma S_lo_le (N : ℕ) (hN : 1 ≤ N) :
    S_lo N ≤ (riemannZeta 9).re := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ge_of_tendsto S_lo_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => S_lo_strictMono.monotone hk⟩)

lemma S_hi_ge (N : ℕ) (hN : 1 ≤ N) :
    (riemannZeta 9).re ≤ S_hi N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact le_of_tendsto S_hi_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => S_hi_strictAnti.antitone hk⟩)

def S_lo_q : ℚ :=
  (range 22).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 9) +
    1 / (8 * 23 ^ 8) + 1 / (2 * 23 ^ 9)

def S_hi_q : ℚ :=
  (range 23).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 9) +
    1 / (8 * 23 ^ 8)

set_option maxHeartbeats 4000000 in
lemma S_lo_q_ge : 10020083928 / 10000000000 ≤ S_lo_q := by norm_num [S_lo_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma S_hi_q_le : S_hi_q ≤ 10020083929 / 10000000000 := by norm_num [S_hi_q, Finset.sum_range_succ]

lemma S_lo_q_cast : (S_lo_q : ℝ) = S_lo 23 := by
  simp only [S_lo_q, S_lo]; push_cast; norm_num

lemma S_hi_q_cast : (S_hi_q : ℝ) = S_hi 23 := by
  simp only [S_hi_q, S_hi]; push_cast; norm_num

lemma S_lo_23_ge : (10020083928 : ℝ) / 10000000000 ≤ S_lo 23 := by
  rw [← S_lo_q_cast,
    show (10020083928 : ℝ) / 10000000000 = ((10020083928 / 10000000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast S_lo_q_ge

lemma S_hi_23_le : S_hi 23 ≤ (10020083929 : ℝ) / 10000000000 := by
  rw [← S_hi_q_cast,
    show (10020083929 : ℝ) / 10000000000 = ((10020083929 / 10000000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast S_hi_q_le

end Zeta9Bounds

open Zeta9Bounds in
theorem zeta9_lo : (10020083928 : ℝ) / 10000000000 ≤ (riemannZeta 9).re :=
  calc (10020083928 : ℝ) / 10000000000
      _ ≤ S_lo 23 := S_lo_23_ge
      _ ≤ (riemannZeta 9).re := S_lo_le 23 (by norm_num)

open Zeta9Bounds in
theorem zeta9_hi : (riemannZeta 9).re ≤ (10020083929 : ℝ) / 10000000000 :=
  calc (riemannZeta 9).re ≤ S_hi 23 := S_hi_ge 23 (by norm_num)
    _ ≤ 10020083929 / 10000000000 := S_hi_23_le
