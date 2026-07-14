import Mathlib

open Real Finset Filter Topology

/-!
# Upper and Lower bounds for π²

## Key theorems

- `pi_sq_lo` : `(9869 : ℝ) / 1000 ≤ Real.pi ^ 2`
- `pi_sq_hi` : `Real.pi ^ 2 ≤ 9876 / 1000`

## Strategy

We use ζ(2) = π²/6 together with Euler-Maclaurin style bounds on ζ(2).
Both bounding sequences are purely rational and converge to ζ(2).
The lower bound is increasing, the upper bound is decreasing.
At N = 23 we verify the numerical bounds via `norm_num` on ℚ,
then multiply by 6 to obtain bounds on π².
-/

namespace PiSqBounds

/-! ## Connection to partial sums via ζ(2) = π²/6 -/

lemma tendsto_partial_sum_inv_sq :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 2)
      atTop (nhds (Real.pi ^ 2 / 6)) := by
  have h := hasSum_zeta_two
  have ht := (hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity) _).mp h
  suffices heq : ∀ N, ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 2 =
      ∑ k ∈ range (N + 1), 1 / (k : ℝ) ^ 2 by
    simp_rw [heq]; exact ht.comp (tendsto_add_atTop_nat 1)
  intro N; rw [sum_range_succ']
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_div,
    inv_zero, add_zero]
  exact sum_congr rfl (fun k _ => by push_cast; ring)

/-! ## Define the bounding sequences -/

/-- Lower bound sequence for ζ(2). Uses N-1 partial sum terms plus
    tail integral 1/N and trapezoid correction 1/(2N²). -/
noncomputable def ζ₂_lo (N : ℕ) : ℝ :=
  (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) +
    1 / (N : ℝ) + 1 / (2 * (N : ℝ) ^ 2)

/-- Upper bound sequence for ζ(2). Uses N partial sum terms plus
    tail integral 1/N. -/
noncomputable def ζ₂_hi (N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) +
    1 / (N : ℝ)

/-! ## Rational fraction identities -/

private lemma lo_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / x ^ 2 + 1 / (x + 1) + 1 / (2 * (x + 1) ^ 2) -
    1 / x - 1 / (2 * x ^ 2) =
    1 / (2 * x ^ 2 * (x + 1) ^ 2) := by
  rw [eq_div_iff (by positivity : 2 * x ^ 2 * (x + 1) ^ 2 ≠ 0)]
  have e1 : 1 / x ^ 2 * (2 * x ^ 2 * (x + 1) ^ 2) = 2 * (x + 1) ^ 2 := by
    rw [one_div, show 2 * x ^ 2 * (x + 1) ^ 2 = x ^ 2 * (2 * (x + 1) ^ 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (x + 1) * (2 * x ^ 2 * (x + 1) ^ 2) = 2 * x ^ 2 * (x + 1) := by
    rw [one_div, show 2 * x ^ 2 * (x + 1) ^ 2 = (x + 1) * (2 * x ^ 2 * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 1) ^ 2) * (2 * x ^ 2 * (x + 1) ^ 2) = x ^ 2 := by
    rw [one_div, show 2 * x ^ 2 * (x + 1) ^ 2 = (2 * (x + 1) ^ 2) * x ^ 2 from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / x * (2 * x ^ 2 * (x + 1) ^ 2) = 2 * x * (x + 1) ^ 2 := by
    rw [one_div, show 2 * x ^ 2 * (x + 1) ^ 2 = x * (2 * x * (x + 1) ^ 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 2) * (2 * x ^ 2 * (x + 1) ^ 2) = (x + 1) ^ 2 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x + 1) ^ 2 + 1 / (x + 1) - 1 / x =
    -1 / (x * (x + 1) ^ 2) := by
  rw [eq_div_iff (by positivity : x * (x + 1) ^ 2 ≠ 0)]
  have e1 : 1 / (x + 1) ^ 2 * (x * (x + 1) ^ 2) = x := by
    rw [one_div, show x * (x + 1) ^ 2 = (x + 1) ^ 2 * x from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (x + 1) * (x * (x + 1) ^ 2) = x * (x + 1) := by
    rw [one_div, show x * (x + 1) ^ 2 = (x + 1) * (x * (x + 1)) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / x * (x * (x + 1) ^ 2) = (x + 1) ^ 2 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

/-! ## Step differences -/

lemma ζ₂_lo_step (N : ℕ) (hN : 1 ≤ N) :
    ζ₂_lo (N + 1) - ζ₂_lo N =
      1 / (2 * (N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range ((N + 1) - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) +
      1 / ((N + 1 : ℕ) : ℝ) + 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2) -
    ((range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) +
      1 / (N : ℝ) + 1 / (2 * (N : ℝ) ^ 2)) =
    1 / (2 * (N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2)
  simp only [show (N + 1 : ℕ) - 1 = N from by omega,
    show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  have hsum : (range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) =
      (range (N - 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) + 1 / (N : ℝ) ^ 2 := by
    conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
    rw [sum_range_succ]
    congr 1
    have h : (↑(N - 1) + 1 : ℝ) = (↑N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
    rw [h]
  conv_lhs => rw [hsum]
  linarith [lo_frac_identity (N : ℝ) hN' hN1]

lemma ζ₂_hi_step (N : ℕ) (hN : 1 ≤ N) :
    ζ₂_hi (N + 1) - ζ₂_hi N =
      -1 / ((N : ℝ) * ((N : ℝ) + 1) ^ 2) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  show (range (N + 1)).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) +
      1 / ((N + 1 : ℕ) : ℝ) -
    ((range N).sum (fun k => 1 / ((k : ℝ) + 1) ^ 2) +
      1 / (N : ℝ)) =
    -1 / ((N : ℝ) * ((N : ℝ) + 1) ^ 2)
  rw [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, sum_range_succ]
  linarith [hi_frac_identity (N : ℝ) hN' hN1]

/-! ## Monotonicity -/

lemma ζ₂_lo_step_pos (N : ℕ) (hN : 1 ≤ N) : ζ₂_lo N < ζ₂_lo (N + 1) := by
  have h := ζ₂_lo_step N hN
  have : (0 : ℝ) < 1 / (2 * N ^ 2 * (N + 1) ^ 2) := by positivity
  linarith

lemma ζ₂_hi_step_neg (N : ℕ) (hN : 1 ≤ N) : ζ₂_hi (N + 1) < ζ₂_hi N := by
  have h := ζ₂_hi_step N hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have : -1 / ((N : ℝ) * ((N : ℝ) + 1) ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

lemma ζ₂_lo_strictMono : StrictMono (fun N => ζ₂_lo (N + 1)) :=
  strictMono_nat_of_lt_succ (fun n => ζ₂_lo_step_pos (n + 1) (by omega))

lemma ζ₂_hi_strictAnti : StrictAnti (fun N => ζ₂_hi (N + 1)) :=
  strictAnti_nat_of_succ_lt (fun n => ζ₂_hi_step_neg (n + 1) (by omega))

/-! ## Convergence -/

private lemma tendsto_inv :
    Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

private lemma tendsto_correction_sq :
    Tendsto (fun N : ℕ => 1 / (2 * ((N : ℝ) + 1) ^ 2)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      ((tendsto_pow_atTop (by omega : 2 ≠ 0)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))

lemma ζ₂_lo_tendsto :
    Tendsto (fun N => ζ₂_lo (N + 1)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  unfold ζ₂_lo
  simp_rw [show ∀ N : ℕ, N + 1 - 1 = N from fun _ => by omega]
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 2) +
      (1 / ((N : ℝ) + 1) + 1 / (2 * ((N : ℝ) + 1) ^ 2)))
      atTop (𝓝 (Real.pi ^ 2 / 6)) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show Real.pi ^ 2 / 6 = Real.pi ^ 2 / 6 + (0 + 0) from by ring]
  exact tendsto_partial_sum_inv_sq.add
    (tendsto_inv.add tendsto_correction_sq)

lemma ζ₂_hi_tendsto :
    Tendsto (fun N => ζ₂_hi (N + 1)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  unfold ζ₂_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1), 1 / ((k : ℝ) + 1) ^ 2) +
      1 / ((N : ℝ) + 1))
      atTop (𝓝 (Real.pi ^ 2 / 6)) by
    exact h.congr (fun n => by push_cast; ring)
  rw [show Real.pi ^ 2 / 6 = Real.pi ^ 2 / 6 + 0 from by ring]
  exact (tendsto_partial_sum_inv_sq.comp (tendsto_add_atTop_nat 1)).add
    tendsto_inv

/-! ## Bounds from monotonicity + convergence -/

lemma ζ₂_lo_le (N : ℕ) (hN : 1 ≤ N) :
    ζ₂_lo N ≤ Real.pi ^ 2 / 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact ge_of_tendsto ζ₂_lo_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ₂_lo_strictMono.monotone hk⟩)

lemma ζ₂_hi_ge (N : ℕ) (hN : 1 ≤ N) :
    Real.pi ^ 2 / 6 ≤ ζ₂_hi N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact le_of_tendsto ζ₂_hi_tendsto
    (eventually_atTop.mpr ⟨m, fun k hk => ζ₂_hi_strictAnti.antitone hk⟩)

/-! ## Computational verification at N = 23 -/

def ζ₂_lo_q : ℚ :=
  (range 22).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 2) +
    1 / 23 + 1 / (2 * 23 ^ 2)

def ζ₂_hi_q : ℚ :=
  (range 23).sum (fun k => 1 / ((k + 1 : ℚ)) ^ 2) +
    1 / 23

set_option maxHeartbeats 4000000 in
lemma ζ₂_lo_q_ge : 9869 / 6000 ≤ ζ₂_lo_q := by norm_num [ζ₂_lo_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma ζ₂_hi_q_le : ζ₂_hi_q ≤ 9876 / 6000 := by norm_num [ζ₂_hi_q, Finset.sum_range_succ]

lemma ζ₂_lo_q_cast : (ζ₂_lo_q : ℝ) = ζ₂_lo 23 := by
  simp only [ζ₂_lo_q, ζ₂_lo]; push_cast; norm_num

lemma ζ₂_hi_q_cast : (ζ₂_hi_q : ℝ) = ζ₂_hi 23 := by
  simp only [ζ₂_hi_q, ζ₂_hi]; push_cast; norm_num

lemma ζ₂_lo_23_ge : (9869 : ℝ) / 6000 ≤ ζ₂_lo 23 := by
  rw [← ζ₂_lo_q_cast,
    show (9869 : ℝ) / 6000 = ((9869 / 6000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ₂_lo_q_ge

lemma ζ₂_hi_23_le : ζ₂_hi 23 ≤ (9876 : ℝ) / 6000 := by
  rw [← ζ₂_hi_q_cast,
    show (9876 : ℝ) / 6000 = ((9876 / 6000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast ζ₂_hi_q_le

/-! ## From ζ(2) bounds to π² bounds -/

lemma six_mul_ζ₂_lo_le : 6 * ζ₂_lo 23 ≤ Real.pi ^ 2 := by
  have h := ζ₂_lo_le 23 (by norm_num)
  linarith

lemma pi_sq_le_six_mul_ζ₂_hi : Real.pi ^ 2 ≤ 6 * ζ₂_hi 23 := by
  have h := ζ₂_hi_ge 23 (by norm_num)
  linarith

end PiSqBounds

open PiSqBounds in
/-- π² is at least 9.869. -/
theorem pi_sq_lo : (9869 : ℝ) / 1000 ≤ Real.pi ^ 2 :=
  calc (9869 : ℝ) / 1000 = 6 * (9869 / 6000) := by ring
    _ ≤ 6 * ζ₂_lo 23 := by linarith [ζ₂_lo_23_ge]
    _ ≤ Real.pi ^ 2 := six_mul_ζ₂_lo_le

open PiSqBounds in
/-- π² is at most 9.876. -/
theorem pi_sq_hi : Real.pi ^ 2 ≤ (9876 : ℝ) / 1000 :=
  calc Real.pi ^ 2 ≤ 6 * ζ₂_hi 23 := pi_sq_le_six_mul_ζ₂_hi
    _ ≤ 6 * (9876 / 6000) := by linarith [ζ₂_hi_23_le]
    _ = 9876 / 1000 := by ring
