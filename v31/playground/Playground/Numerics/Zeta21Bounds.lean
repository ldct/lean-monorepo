import Mathlib


open Real Finset Filter Topology

/-!
# Upper and Lower bounds for ζ(21)

## Key theorems

- `zeta21_lo` : `(10000004769 : ℝ) / 10000000000 ≤ (riemannZeta 21).re`
- `zeta21_hi` : `(riemannZeta 21).re ≤ (10000004770 : ℝ) / 10000000000`

Same Euler-Maclaurin approach as Zeta3Bounds. N = 23 gives 10 decimal places.
-/

namespace Zeta21Bounds

lemma summable_real :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 21) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 21) :=
    (Real.summable_one_div_nat_pow (p := 21)).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 21) 1).mpr h).congr
    (fun n => by congr 1; push_cast; ring)

private lemma summable_cpow :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (21 : ℂ)) := by
  have hrec : 1 < (21 : ℂ).re := by simp
  rw [show (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (21 : ℂ)) =
    (fun n : ℕ => 1 / (n : ℂ) ^ (21 : ℂ)) ∘ (· + 1) from by ext; simp]
  exact (Complex.summable_one_div_nat_cpow.mpr hrec).comp_injective (fun _ _ h => by omega)

lemma re_eq_tsum :
    (riemannZeta 21).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 21 := by
  have hrec : 1 < (21 : ℂ).re := by simp
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hrec
  have hterm_re : ∀ n : ℕ, (1 / ((n : ℂ) + 1) ^ (21 : ℂ)).re = 1 / ((n : ℝ) + 1) ^ 21 := by
    intro n
    rw [show ((n : ℂ) + 1) ^ (21 : ℂ) = ((((n : ℝ) + 1) ^ 21 : ℝ) : ℂ) from by
      rw [show (21 : ℂ) = ((21 : ℕ) : ℂ) from by norm_cast, Complex.cpow_natCast]; push_cast; ring]
    rw [show (1 : ℂ) / ((((n : ℝ) + 1) ^ 21 : ℝ) : ℂ) = ((1 / ((n : ℝ) + 1) ^ 21 : ℝ) : ℂ) from by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [hzeta, Complex.re_tsum summable_cpow]
  congr 1; ext n; exact hterm_re n

lemma tendsto_partial_sum :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 21)
      atTop (𝓝 (riemannZeta 21).re) := by
  rw [← hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  rw [re_eq_tsum]; exact summable_real.hasSum

noncomputable def S_lo (N : ℕ) : ℝ :=
  (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) +
    1 / (20 * (N : ℝ) ^ 20) + 1 / (2 * (N : ℝ) ^ 21)

noncomputable def S_hi (N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) +
    1 / (20 * (N : ℝ) ^ 20)

private lemma lo_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x ^ 21 + 1 / (20 * (x + 1) ^ 20) + 1 / (2 * (x + 1) ^ 21) -
    1 / (20 * x ^ 20) - 1 / (2 * x ^ 21) =
    (2 * x + 1) * (10 + 189 * x + 1701 * x ^ 2 + 9688 * x ^ 3 + 39144 * x ^ 4 + 119217 * x ^ 5 + 283857 * x ^ 6 + 540822 * x ^ 7 + 836976 * x ^ 8 + 1061858 * x ^ 9 + 1109514 * x ^ 10 + 955416 * x ^ 11 + 675752 * x ^ 12 + 389466 * x ^ 13 + 180378 * x ^ 14 + 65604 * x ^ 15 + 18018 * x ^ 16 + 3465 * x ^ 17 + 385 * x ^ 18) /
      (20 * x ^ 21 * (x + 1) ^ 21) := by
  rw [eq_div_iff (by positivity : (20 : ℝ) * x ^ 21 * (x + 1) ^ 21 ≠ 0)]
  have e1 : 1 / x ^ 21 * (20 * x ^ 21 * (x + 1) ^ 21) = 20 * (x + 1) ^ 21 := by
    rw [one_div, show 20 * x ^ 21 * (x + 1) ^ 21 = x ^ 21 * (20 * (x + 1) ^ 21) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (20 * (x + 1) ^ 20) * (20 * x ^ 21 * (x + 1) ^ 21) = x ^ 21 * (x + 1) := by
    rw [one_div, show 20 * x ^ 21 * (x + 1) ^ 21 = (20 * (x + 1) ^ 20) * (x ^ 21 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ 21) * (20 * x ^ 21 * (x + 1) ^ 21) = 20 * x ^ 21 / 2 := by
    rw [one_div, show 20 * x ^ 21 * (x + 1) ^ 21 = (2 * (x + 1) ^ 21) * (20 * x ^ 21 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / (20 * x ^ 20) * (20 * x ^ 21 * (x + 1) ^ 21) = x * (x + 1) ^ 21 := by
    rw [one_div, show 20 * x ^ 21 * (x + 1) ^ 21 = (20 * x ^ 20) * (x * (x + 1) ^ 21) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 21) * (20 * x ^ 21 * (x + 1) ^ 21) = 20 * (x + 1) ^ 21 / 2 := by
    rw [one_div, show 20 * x ^ 21 * (x + 1) ^ 21 = (2 * x ^ 21) * (20 * (x + 1) ^ 21 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) ^ 21 + 1 / (20 * (x + 1) ^ 20) - 1 / (20 * x ^ 20) =
    -(1 + 21 * x + 210 * x ^ 2 + 1330 * x ^ 3 + 5985 * x ^ 4 + 20349 * x ^ 5 + 54264 * x ^ 6 + 116280 * x ^ 7 + 203490 * x ^ 8 + 293930 * x ^ 9 + 352716 * x ^ 10 + 352716 * x ^ 11 + 293930 * x ^ 12 + 203490 * x ^ 13 + 116280 * x ^ 14 + 54264 * x ^ 15 + 20349 * x ^ 16 + 5985 * x ^ 17 + 1330 * x ^ 18 + 210 * x ^ 19) /
      (20 * x ^ 20 * (x + 1) ^ 21) := by
  rw [eq_div_iff (by positivity : (20 : ℝ) * x ^ 20 * (x + 1) ^ 21 ≠ 0)]
  have e1 : 1 / (x + 1) ^ 21 * (20 * x ^ 20 * (x + 1) ^ 21) = 20 * x ^ 20 := by
    rw [one_div, show 20 * x ^ 20 * (x + 1) ^ 21 = (x + 1) ^ 21 * (20 * x ^ 20) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (20 * (x + 1) ^ 20) * (20 * x ^ 20 * (x + 1) ^ 21) = x ^ 20 * (x + 1) := by
    rw [one_div, show 20 * x ^ 20 * (x + 1) ^ 21 = (20 * (x + 1) ^ 20) * (x ^ 20 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (20 * x ^ 20) * (20 * x ^ 20 * (x + 1) ^ 21) = (x + 1) ^ 21 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

lemma S_lo_step (N : ℕ) (hN : 1 ≤ N) :
    S_lo (N + 1) - S_lo N =
      (2 * (N : ℝ) + 1) * (10 + 189 * (N : ℝ) + 1701 * (N : ℝ) ^ 2 + 9688 * (N : ℝ) ^ 3 + 39144 * (N : ℝ) ^ 4 + 119217 * (N : ℝ) ^ 5 + 283857 * (N : ℝ) ^ 6 + 540822 * (N : ℝ) ^ 7 + 836976 * (N : ℝ) ^ 8 + 1061858 * (N : ℝ) ^ 9 + 1109514 * (N : ℝ) ^ 10 + 955416 * (N : ℝ) ^ 11 + 675752 * (N : ℝ) ^ 12 + 389466 * (N : ℝ) ^ 13 + 180378 * (N : ℝ) ^ 14 + 65604 * (N : ℝ) ^ 15 + 18018 * (N : ℝ) ^ 16 + 3465 * (N : ℝ) ^ 17 + 385 * (N : ℝ) ^ 18) /
        (20 * (N : ℝ) ^ 21 * ((N : ℝ) + 1) ^ 21) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) +
      1 / (20 * ((N + 1 : ℕ) : ℝ) ^ 20) + 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 21) -
    ((range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) +
      1 / (20 * (N : ℝ) ^ 20) + 1 / (2 * (N : ℝ) ^ 21)) =
    (2 * (N : ℝ) + 1) * (10 + 189 * (N : ℝ) + 1701 * (N : ℝ) ^ 2 + 9688 * (N : ℝ) ^ 3 + 39144 * (N : ℝ) ^ 4 + 119217 * (N : ℝ) ^ 5 + 283857 * (N : ℝ) ^ 6 + 540822 * (N : ℝ) ^ 7 + 836976 * (N : ℝ) ^ 8 + 1061858 * (N : ℝ) ^ 9 + 1109514 * (N : ℝ) ^ 10 + 955416 * (N : ℝ) ^ 11 + 675752 * (N : ℝ) ^ 12 + 389466 * (N : ℝ) ^ 13 + 180378 * (N : ℝ) ^ 14 + 65604 * (N : ℝ) ^ 15 + 18018 * (N : ℝ) ^ 16 + 3465 * (N : ℝ) ^ 17 + 385 * (N : ℝ) ^ 18) /
      (20 * (N : ℝ) ^ 21 * ((N : ℝ) + 1) ^ 21)
  simp only [show (N + 1 : ℕ) - 1 = N from by omega,
    show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) =
      (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) + 1 / (N : ℝ) ^ 21 := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (↑(N - 1) + 1 : ℝ) = (↑N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : ℝ) hN' hN1]

lemma S_hi_step (N : ℕ) (hN : 1 ≤ N) :
    S_hi (N + 1) - S_hi N =
      -(1 + 21 * (N : ℝ) + 210 * (N : ℝ) ^ 2 + 1330 * (N : ℝ) ^ 3 + 5985 * (N : ℝ) ^ 4 + 20349 * (N : ℝ) ^ 5 + 54264 * (N : ℝ) ^ 6 + 116280 * (N : ℝ) ^ 7 + 203490 * (N : ℝ) ^ 8 + 293930 * (N : ℝ) ^ 9 + 352716 * (N : ℝ) ^ 10 + 352716 * (N : ℝ) ^ 11 + 293930 * (N : ℝ) ^ 12 + 203490 * (N : ℝ) ^ 13 + 116280 * (N : ℝ) ^ 14 + 54264 * (N : ℝ) ^ 15 + 20349 * (N : ℝ) ^ 16 + 5985 * (N : ℝ) ^ 17 + 1330 * (N : ℝ) ^ 18 + 210 * (N : ℝ) ^ 19) /
        (20 * (N : ℝ) ^ 20 * ((N : ℝ) + 1) ^ 21) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) +
      1 / (20 * ((N + 1 : ℕ) : ℝ) ^ 20) -
    ((range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 21) +
      1 / (20 * (N : ℝ) ^ 20)) =
    -(1 + 21 * (N : ℝ) + 210 * (N : ℝ) ^ 2 + 1330 * (N : ℝ) ^ 3 + 5985 * (N : ℝ) ^ 4 + 20349 * (N : ℝ) ^ 5 + 54264 * (N : ℝ) ^ 6 + 116280 * (N : ℝ) ^ 7 + 203490 * (N : ℝ) ^ 8 + 293930 * (N : ℝ) ^ 9 + 352716 * (N : ℝ) ^ 10 + 352716 * (N : ℝ) ^ 11 + 293930 * (N : ℝ) ^ 12 + 203490 * (N : ℝ) ^ 13 + 116280 * (N : ℝ) ^ 14 + 54264 * (N : ℝ) ^ 15 + 20349 * (N : ℝ) ^ 16 + 5985 * (N : ℝ) ^ 17 + 1330 * (N : ℝ) ^ 18 + 210 * (N : ℝ) ^ 19) /
      (20 * (N : ℝ) ^ 20 * ((N : ℝ) + 1) ^ 21)
  rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : ℝ) hN' hN1]

lemma S_lo_step_pos (N : ℕ) (hN : 1 ≤ N) : S_lo N < S_lo (N + 1) := by
  have h := S_lo_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : (0 : ℝ) < (2 * N + 1) * (10 + 189 * (N : ℝ) + 1701 * (N : ℝ) ^ 2 + 9688 * (N : ℝ) ^ 3 + 39144 * (N : ℝ) ^ 4 + 119217 * (N : ℝ) ^ 5 + 283857 * (N : ℝ) ^ 6 + 540822 * (N : ℝ) ^ 7 + 836976 * (N : ℝ) ^ 8 + 1061858 * (N : ℝ) ^ 9 + 1109514 * (N : ℝ) ^ 10 + 955416 * (N : ℝ) ^ 11 + 675752 * (N : ℝ) ^ 12 + 389466 * (N : ℝ) ^ 13 + 180378 * (N : ℝ) ^ 14 + 65604 * (N : ℝ) ^ 15 + 18018 * (N : ℝ) ^ 16 + 3465 * (N : ℝ) ^ 17 + 385 * (N : ℝ) ^ 18) /
      (20 * N ^ 21 * (N + 1) ^ 21) := by positivity
  linarith

lemma S_hi_step_neg (N : ℕ) (hN : 1 ≤ N) : S_hi (N + 1) < S_hi N := by
  have h := S_hi_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hnum : (1 + 21 * (N : ℝ) + 210 * (N : ℝ) ^ 2 + 1330 * (N : ℝ) ^ 3 + 5985 * (N : ℝ) ^ 4 + 20349 * (N : ℝ) ^ 5 + 54264 * (N : ℝ) ^ 6 + 116280 * (N : ℝ) ^ 7 + 203490 * (N : ℝ) ^ 8 + 293930 * (N : ℝ) ^ 9 + 352716 * (N : ℝ) ^ 10 + 352716 * (N : ℝ) ^ 11 + 293930 * (N : ℝ) ^ 12 + 203490 * (N : ℝ) ^ 13 + 116280 * (N : ℝ) ^ 14 + 54264 * (N : ℝ) ^ 15 + 20349 * (N : ℝ) ^ 16 + 5985 * (N : ℝ) ^ 17 + 1330 * (N : ℝ) ^ 18 + 210 * (N : ℝ) ^ 19) > 0 := by positivity
  have : -(1 + 21 * (N : ℝ) + 210 * (N : ℝ) ^ 2 + 1330 * (N : ℝ) ^ 3 + 5985 * (N : ℝ) ^ 4 + 20349 * (N : ℝ) ^ 5 + 54264 * (N : ℝ) ^ 6 + 116280 * (N : ℝ) ^ 7 + 203490 * (N : ℝ) ^ 8 + 293930 * (N : ℝ) ^ 9 + 352716 * (N : ℝ) ^ 10 + 352716 * (N : ℝ) ^ 11 + 293930 * (N : ℝ) ^ 12 + 203490 * (N : ℝ) ^ 13 + 116280 * (N : ℝ) ^ 14 + 54264 * (N : ℝ) ^ 15 + 20349 * (N : ℝ) ^ 16 + 5985 * (N : ℝ) ^ 17 + 1330 * (N : ℝ) ^ 18 + 210 * (N : ℝ) ^ 19) /
      (20 * (N : ℝ) ^ 20 * ((N : ℝ) + 1) ^ 21) < 0 :=
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
    Tendsto (fun N => S_lo (N + 1)) atTop (𝓝 (riemannZeta 21).re) := by
  unfold S_lo
  simp_rw [show ∀ N : ℕ, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 21) +
      (1 / (20 * ((N : ℝ) + 1) ^ 20) + 1 / (2 * ((N : ℝ) + 1) ^ 21)))
      atTop (𝓝 (riemannZeta 21).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 21).re = (riemannZeta 21).re + (0 + 0) from by ring]
  exact tendsto_partial_sum.add
    ((tendsto_correction 20 (by norm_num) 20 (by norm_num)).add
      (tendsto_correction 2 (by norm_num) 21 (by norm_num)))

lemma S_hi_tendsto :
    Tendsto (fun N => S_hi (N + 1)) atTop (𝓝 (riemannZeta 21).re) := by
  unfold S_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 21) +
      1 / (20 * ((N : ℝ) + 1) ^ 20))
      atTop (𝓝 (riemannZeta 21).re) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show (riemannZeta 21).re = (riemannZeta 21).re + 0 from by ring]
  exact (tendsto_partial_sum.comp (tendsto_add_atTop_nat 1)).add
    (tendsto_correction 20 (by norm_num) 20 (by norm_num))

lemma S_lo_le (N : ℕ) (hN : 1 ≤ N) :
    S_lo N ≤ (riemannZeta 21).re := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ge_of_tendsto S_lo_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => S_lo_strictMono.monotone hk⟩)

lemma S_hi_ge (N : ℕ) (hN : 1 ≤ N) :
    (riemannZeta 21).re ≤ S_hi N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact le_of_tendsto S_hi_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => S_hi_strictAnti.antitone hk⟩)

def S_lo_q : ℚ :=
  (range 22).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 21) +
    1 / (20 * 23 ^ 20) + 1 / (2 * 23 ^ 21)

def S_hi_q : ℚ :=
  (range 23).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 21) +
    1 / (20 * 23 ^ 20)

set_option maxHeartbeats 4000000 in
lemma S_lo_q_ge : 10000004769 / 10000000000 ≤ S_lo_q := by norm_num [S_lo_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma S_hi_q_le : S_hi_q ≤ 10000004770 / 10000000000 := by norm_num [S_hi_q, Finset.sum_range_succ]

lemma S_lo_q_cast : (S_lo_q : ℝ) = S_lo 23 := by
  simp only [S_lo_q, S_lo]; push_cast; norm_num

lemma S_hi_q_cast : (S_hi_q : ℝ) = S_hi 23 := by
  simp only [S_hi_q, S_hi]; push_cast; norm_num

lemma S_lo_23_ge : (10000004769 : ℝ) / 10000000000 ≤ S_lo 23 := by
  rw [← S_lo_q_cast,
    show (10000004769 : ℝ) / 10000000000 = ((10000004769 / 10000000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast S_lo_q_ge

lemma S_hi_23_le : S_hi 23 ≤ (10000004770 : ℝ) / 10000000000 := by
  rw [← S_hi_q_cast,
    show (10000004770 : ℝ) / 10000000000 = ((10000004770 / 10000000000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast S_hi_q_le

end Zeta21Bounds

open Zeta21Bounds in
theorem zeta21_lo : (10000004769 : ℝ) / 10000000000 ≤ (riemannZeta 21).re :=
  calc (10000004769 : ℝ) / 10000000000
      _ ≤ S_lo 23 := S_lo_23_ge
      _ ≤ (riemannZeta 21).re := S_lo_le 23 (by norm_num)

open Zeta21Bounds in
theorem zeta21_hi : (riemannZeta 21).re ≤ (10000004770 : ℝ) / 10000000000 :=
  calc (riemannZeta 21).re ≤ S_hi 23 := S_hi_ge 23 (by norm_num)
    _ ≤ 10000004770 / 10000000000 := S_hi_23_le
