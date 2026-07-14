import Mathlib


open Real Finset Filter Topology

/-!
# Upper and Lower bounds for ζ(11)

## Key theorems

- `zeta11_lo` : `(10004941886 : ℝ) / 10000000000 ≤ (riemannZeta 11).re`
- `zeta11_hi` : `(riemannZeta 11).re ≤ (10004941887 : ℝ) / 10000000000`

Same Euler-Maclaurin approach as Zeta3Bounds. N = 23 gives 10 decimal places.
-/

namespace Zeta11Bounds

lemma summable_real :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 11) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 11) :=
    (Real.summable_one_div_nat_pow (p := 11)).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 11) 1).mpr h).congr
    (fun n => by congr 1; push_cast; ring)

private lemma summable_cpow :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (11 : ℂ)) := by
  have hrec : 1 < (11 : ℂ).re := by simp
  rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (11 : ℂ)) =
    (fun n : ℕ => 1 / (n : ℂ) ^ (11 : ℂ)) ∘ (· + 1) from by ext; simp]
  exact (Complex.summable_one_div_nat_cpow.mpr hrec).comp_injective (fun _ _ h => by omega)

lemma re_eq_tsum :
    (riemannZeta 11).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 11 := by
  have hrec : 1 < (11 : ℂ).re := by simp
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hrec
  have hterm_re : ∀ n : ℕ, (1 / ((n : ℂ) + 1) ^ (11 : ℂ)).re = 1 / ((n : ℝ) + 1) ^ 11 := by
    intro n
    rw [show ((n : ℂ) + 1) ^ (11 : ℂ) = ((((n : ℝ) + 1) ^ 11 : ℝ) : ℂ) from by
      rw [show (11 : ℂ) = ((11 : ℕ) : ℂ) from by norm_cast, Complex.cpow_natCast]; push_cast; ring]
    rw [show (1 : ℂ) / ((((n : ℝ) + 1) ^ 11 : ℝ) : ℂ) = ((1 / ((n : ℝ) + 1) ^ 11 : ℝ) : ℂ) from by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [hzeta, Complex.re_tsum summable_cpow]
  congr 1; ext n; exact hterm_re n

lemma tendsto_partial_sum :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 11)
      atTop (𝓝 (riemannZeta 11).re) := by
  rw [← hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  rw [re_eq_tsum]; exact summable_real.hasSum

noncomputable def S_lo (N : ℕ) : ℝ :=
  (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) +
    1 / (10 * (N : ℝ) ^ 10) + 1 / (2 * (N : ℝ) ^ 11)

noncomputable def S_hi (N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) +
    1 / (10 * (N : ℝ) ^ 10)

private lemma lo_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x ^ 11 + 1 / (10 * (x + 1) ^ 10) + 1 / (2 * (x + 1) ^ 11) -
    1 / (10 * x ^ 10) - 1 / (2 * x ^ 11) =
    (2 * x + 1) * (5 + 44 * x + 176 * x ^ 2 + 418 * x ^ 3 + 649 * x ^ 4 + 682 * x ^ 5 + 484 * x ^ 6 + 220 * x ^ 7 + 55 * x ^ 8) /
      (10 * x ^ 11 * (x + 1) ^ 11) := by
  rw [eq_div_iff (by positivity : (10 : ℝ) * x ^ 11 * (x + 1) ^ 11 ≠ 0)]
  have e1 : 1 / x ^ 11 * (10 * x ^ 11 * (x + 1) ^ 11) = 10 * (x + 1) ^ 11 := by
    rw [one_div, show 10 * x ^ 11 * (x + 1) ^ 11 = x ^ 11 * (10 * (x + 1) ^ 11) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (10 * (x + 1) ^ 10) * (10 * x ^ 11 * (x + 1) ^ 11) = x ^ 11 * (x + 1) := by
    rw [one_div, show 10 * x ^ 11 * (x + 1) ^ 11 = (10 * (x + 1) ^ 10) * (x ^ 11 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ 11) * (10 * x ^ 11 * (x + 1) ^ 11) = 10 * x ^ 11 / 2 := by
    rw [one_div, show 10 * x ^ 11 * (x + 1) ^ 11 = (2 * (x + 1) ^ 11) * (10 * x ^ 11 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / (10 * x ^ 10) * (10 * x ^ 11 * (x + 1) ^ 11) = x * (x + 1) ^ 11 := by
    rw [one_div, show 10 * x ^ 11 * (x + 1) ^ 11 = (10 * x ^ 10) * (x * (x + 1) ^ 11) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 11) * (10 * x ^ 11 * (x + 1) ^ 11) = 10 * (x + 1) ^ 11 / 2 := by
    rw [one_div, show 10 * x ^ 11 * (x + 1) ^ 11 = (2 * x ^ 11) * (10 * (x + 1) ^ 11 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) ^ 11 + 1 / (10 * (x + 1) ^ 10) - 1 / (10 * x ^ 10) =
    -(1 + 11 * x + 55 * x ^ 2 + 165 * x ^ 3 + 330 * x ^ 4 + 462 * x ^ 5 + 462 * x ^ 6 + 330 * x ^ 7 + 165 * x ^ 8 + 55 * x ^ 9) /
      (10 * x ^ 10 * (x + 1) ^ 11) := by
  rw [eq_div_iff (by positivity : (10 : ℝ) * x ^ 10 * (x + 1) ^ 11 ≠ 0)]
  have e1 : 1 / (x + 1) ^ 11 * (10 * x ^ 10 * (x + 1) ^ 11) = 10 * x ^ 10 := by
    rw [one_div, show 10 * x ^ 10 * (x + 1) ^ 11 = (x + 1) ^ 11 * (10 * x ^ 10) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (10 * (x + 1) ^ 10) * (10 * x ^ 10 * (x + 1) ^ 11) = x ^ 10 * (x + 1) := by
    rw [one_div, show 10 * x ^ 10 * (x + 1) ^ 11 = (10 * (x + 1) ^ 10) * (x ^ 10 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (10 * x ^ 10) * (10 * x ^ 10 * (x + 1) ^ 11) = (x + 1) ^ 11 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

lemma S_lo_step (N : ℕ) (hN : 1 ≤ N) :
    S_lo (N + 1) - S_lo N =
      (2 * (N : ℝ) + 1) * (5 + 44 * (N : ℝ) + 176 * (N : ℝ) ^ 2 + 418 * (N : ℝ) ^ 3 + 649 * (N : ℝ) ^ 4 + 682 * (N : ℝ) ^ 5 + 484 * (N : ℝ) ^ 6 + 220 * (N : ℝ) ^ 7 + 55 * (N : ℝ) ^ 8) /
        (10 * (N : ℝ) ^ 11 * ((N : ℝ) + 1) ^ 11) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) +
      1 / (10 * ((N + 1 : ℕ) : ℝ) ^ 10) + 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 11) -
    ((range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) +
      1 / (10 * (N : ℝ) ^ 10) + 1 / (2 * (N : ℝ) ^ 11)) =
    (2 * (N : ℝ) + 1) * (5 + 44 * (N : ℝ) + 176 * (N : ℝ) ^ 2 + 418 * (N : ℝ) ^ 3 + 649 * (N : ℝ) ^ 4 + 682 * (N : ℝ) ^ 5 + 484 * (N : ℝ) ^ 6 + 220 * (N : ℝ) ^ 7 + 55 * (N : ℝ) ^ 8) /
      (10 * (N : ℝ) ^ 11 * ((N : ℝ) + 1) ^ 11)
  simp only [show (N + 1 : ℕ) - 1 = N from by omega,
    show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) =
      (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) + 1 / (N : ℝ) ^ 11 := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (↑(N - 1) + 1 : ℝ) = (↑N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : ℝ) hN' hN1]

lemma S_hi_step (N : ℕ) (hN : 1 ≤ N) :
    S_hi (N + 1) - S_hi N =
      -(1 + 11 * (N : ℝ) + 55 * (N : ℝ) ^ 2 + 165 * (N : ℝ) ^ 3 + 330 * (N : ℝ) ^ 4 + 462 * (N : ℝ) ^ 5 + 462 * (N : ℝ) ^ 6 + 330 * (N : ℝ) ^ 7 + 165 * (N : ℝ) ^ 8 + 55 * (N : ℝ) ^ 9) /
        (10 * (N : ℝ) ^ 10 * ((N : ℝ) + 1) ^ 11) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) +
      1 / (10 * ((N + 1 : ℕ) : ℝ) ^ 10) -
    ((range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 11) +
      1 / (10 * (N : ℝ) ^ 10)) =
    -(1 + 11 * (N : ℝ) + 55 * (N : ℝ) ^ 2 + 165 * (N : ℝ) ^ 3 + 330 * (N : ℝ) ^ 4 + 462 * (N : ℝ) ^ 5 + 462 * (N : ℝ) ^ 6 + 330 * (N : ℝ) ^ 7 + 165 * (N : ℝ) ^ 8 + 55 * (N : ℝ) ^ 9) /
      (10 * (N : ℝ) ^ 10 * ((N : ℝ) + 1) ^ 11)
  rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : ℝ) hN' hN1]

lemma S_lo_step_pos (N : ℕ) (hN : 1 ≤ N) : S_lo N < S_lo (N + 1) := by
  have h := S_lo_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : (0 : ℝ) < (2 * N + 1) * (5 + 44 * (N : ℝ) + 176 * (N : ℝ) ^ 2 + 418 * (N : ℝ) ^ 3 + 649 * (N : ℝ) ^ 4 + 682 * (N : ℝ) ^ 5 + 484 * (N : ℝ) ^ 6 + 220 * (N : ℝ) ^ 7 + 55 * (N : ℝ) ^ 8) /
      (10 * N ^ 11 * (N + 1) ^ 11) := by positivity
  linarith

lemma S_hi_step_neg (N : ℕ) (hN : 1 ≤ N) : S_hi (N + 1) < S_hi N := by
  have h := S_hi_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hnum : (1 + 11 * (N : ℝ) + 55 * (N : ℝ) ^ 2 + 165 * (N : ℝ) ^ 3 + 330 * (N : ℝ) ^ 4 + 462 * (N : ℝ) ^ 5 + 462 * (N : ℝ) ^ 6 + 330 * (N : ℝ) ^ 7 + 165 * (N : ℝ) ^ 8 + 55 * (N : ℝ) ^ 9) > 0 := by positivity
  have : -(1 + 11 * (N : ℝ) + 55 * (N : ℝ) ^ 2 + 165 * (N : ℝ) ^ 3 + 330 * (N : ℝ) ^ 4 + 462 * (N : ℝ) ^ 5 + 462 * (N : ℝ) ^ 6 + 330 * (N : ℝ) ^ 7 + 165 * (N : ℝ) ^ 8 + 55 * (N : ℝ) ^ 9) /
      (10 * (N : ℝ) ^ 10 * ((N : ℝ) + 1) ^ 11) < 0 :=
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
    Tendsto (fun N => S_lo (N + 1)) atTop (𝓝 (riemannZeta 11).re) := by
  unfold S_lo
  simp_rw [show ∀ N : ℕ, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 11) +
      (1 / (10 * ((N : ℝ) + 1) ^ 10) + 1 / (2 * ((N : ℝ) + 1) ^ 11)))
      atTop (𝓝 (riemannZeta 11).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 11).re = (riemannZeta 11).re + (0 + 0) from by ring]
  exact tendsto_partial_sum.add
    ((tendsto_correction 10 (by norm_num) 10 (by norm_num)).add
      (tendsto_correction 2 (by norm_num) 11 (by norm_num)))

lemma S_hi_tendsto :
    Tendsto (fun N => S_hi (N + 1)) atTop (𝓝 (riemannZeta 11).re) := by
  unfold S_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 11) +
      1 / (10 * ((N : ℝ) + 1) ^ 10))
      atTop (𝓝 (riemannZeta 11).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 11).re = (riemannZeta 11).re + 0 from by ring]
  exact (tendsto_partial_sum.comp (tendsto_add_atTop_nat 1)).add
    (tendsto_correction 10 (by norm_num) 10 (by norm_num))

lemma S_lo_le (N : ℕ) (hN : 1 ≤ N) :
    S_lo N ≤ (riemannZeta 11).re := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ge_of_tendsto S_lo_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => S_lo_strictMono.monotone hk⟩)

lemma S_hi_ge (N : ℕ) (hN : 1 ≤ N) :
    (riemannZeta 11).re ≤ S_hi N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact le_of_tendsto S_hi_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => S_hi_strictAnti.antitone hk⟩)

def S_lo_q : ℚ :=
  (range 22).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 11) +
    1 / (10 * 23 ^ 10) + 1 / (2 * 23 ^ 11)

def S_hi_q : ℚ :=
  (range 23).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 11) +
    1 / (10 * 23 ^ 10)

set_option maxHeartbeats 4000000 in
lemma S_lo_q_ge : 10004941886 / 10000000000 ≤ S_lo_q := by norm_num [S_lo_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma S_hi_q_le : S_hi_q ≤ 10004941887 / 10000000000 := by norm_num [S_hi_q, Finset.sum_range_succ]

lemma S_lo_q_cast : (S_lo_q : ℝ) = S_lo 23 := by
  simp only [S_lo_q, S_lo]; push_cast; norm_num

lemma S_hi_q_cast : (S_hi_q : ℝ) = S_hi 23 := by
  simp only [S_hi_q, S_hi]; push_cast; norm_num

lemma S_lo_23_ge : (10004941886 : ℝ) / 10000000000 ≤ S_lo 23 := by
  rw [← S_lo_q_cast,
    show (10004941886 : ℝ) / 10000000000 = ((10004941886 / 10000000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast S_lo_q_ge

lemma S_hi_23_le : S_hi 23 ≤ (10004941887 : ℝ) / 10000000000 := by
  rw [← S_hi_q_cast,
    show (10004941887 : ℝ) / 10000000000 = ((10004941887 / 10000000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast S_hi_q_le

end Zeta11Bounds

open Zeta11Bounds in
theorem zeta11_lo : (10004941886 : ℝ) / 10000000000 ≤ (riemannZeta 11).re :=
  calc (10004941886 : ℝ) / 10000000000
      _ ≤ S_lo 23 := S_lo_23_ge
      _ ≤ (riemannZeta 11).re := S_lo_le 23 (by norm_num)

open Zeta11Bounds in
theorem zeta11_hi : (riemannZeta 11).re ≤ (10004941887 : ℝ) / 10000000000 :=
  calc (riemannZeta 11).re ≤ S_hi 23 := S_hi_ge 23 (by norm_num)
    _ ≤ 10004941887 / 10000000000 := S_hi_23_le
