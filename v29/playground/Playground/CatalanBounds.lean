import Mathlib

open Real Finset Filter Topology

/-!
# Upper and Lower bounds for Catalan's constant

## Key theorems

- `catalan_lo` : `(9159 : ℝ) / 10000 ≤ catalanConstant`
- `catalan_hi` : `catalanConstant ≤ (9161 : ℝ) / 10000`

## Strategy

Catalan's constant is G = Σ (-1)ⁿ/(2n+1)² = P - Q where
  P = Σ 1/(4k+1)²   and   Q = Σ 1/(4k+3)².

We bound P and Q separately using Euler-Maclaurin style integral comparison.
Both bounding sequences are purely rational. At N = 23 we verify numerical
bounds via `norm_num` on ℚ.

The bounding sequences for S(a) = Σ_{k=0}^\infty 1/(4k+a)² are:
- S_lo(a, N) = Σ_{k=0}^{N-1} 1/(4k+a)² + 1/(4(4N+a)) + 1/(2(4N+a)²)  (increasing)
- S_hi(a, N) = Σ_{k=0}^{N} 1/(4k+a)² + 1/(4(4N+a))                      (decreasing)

Step identities (with x = 4N+a):
- S_lo step = 8/(x²(x+4)²) > 0
- S_hi step = -4/(x(x+4)²) < 0

Then catalan_lo = S_lo(1,23) - S_hi(3,23) and catalan_hi = S_hi(1,23) - S_lo(3,23).
-/

namespace CatalanBounds

/-! ## Summability and convergence -/

private lemma summable_inv_sq_add_one :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  exact ((summable_nat_add_iff (f := fun n => 1 / (n : ℝ) ^ 2) 1).mpr this).congr
    (fun n => by push_cast; ring)

lemma summable_inv_sq_arith (a : ℕ) (ha : 0 < a) :
    Summable (fun k : ℕ => 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) := by
  apply summable_inv_sq_add_one.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hle : (k : ℝ) + 1 ≤ 4 * (k : ℝ) + (a : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  show 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2 ≤ 1 / ((k : ℝ) + 1) ^ 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [one_mul]
  exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) hle 2

lemma tendsto_partial_sum (a : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2)
      atTop (𝓝 (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2)) := by
  rw [← hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  exact (summable_inv_sq_arith a ha).hasSum

/-! ## Define the bounding sequences -/

/-- Lower bound sequence for S(a) = ∑ 1/(4k+a)². Uses N partial sum terms plus
    tail integral 1/(4(4N+a)) and trapezoid correction 1/(2(4N+a)²). -/
noncomputable def S_lo (a N : ℕ) : ℝ :=
  (range N).sum (fun k => 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
    1 / (4 * (4 * (N : ℝ) + (a : ℝ))) + 1 / (2 * (4 * (N : ℝ) + (a : ℝ)) ^ 2)

/-- Upper bound sequence for S(a) = ∑ 1/(4k+a)². Uses N+1 partial sum terms plus
    tail integral 1/(4(4N+a)). -/
noncomputable def S_hi (a N : ℕ) : ℝ :=
  (range (N + 1)).sum (fun k => 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
    1 / (4 * (4 * (N : ℝ) + (a : ℝ)))

/-! ## Rational fraction identities

The shift is always +4 (from 4k+a to 4(k+1)+a = 4k+a+4).
So both identities are in terms of x and x+4. -/

private lemma lo_frac_identity (x : ℝ) (hx : 0 < x) :
    1 / x ^ 2 + 1 / (4 * (x + 4)) + 1 / (2 * (x + 4) ^ 2) -
    1 / (4 * x) - 1 / (2 * x ^ 2) =
    8 / (x ^ 2 * (x + 4) ^ 2) := by
  have hx4 : (0 : ℝ) < x + 4 := by linarith
  rw [eq_div_iff (by positivity : x ^ 2 * (x + 4) ^ 2 ≠ 0)]
  have e1 : 1 / x ^ 2 * (x ^ 2 * (x + 4) ^ 2) = (x + 4) ^ 2 := by
    rw [one_div, inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (4 * (x + 4)) * (x ^ 2 * (x + 4) ^ 2) = x ^ 2 * (x + 4) / 4 := by
    rw [one_div, show x ^ 2 * (x + 4) ^ 2 = (4 * (x + 4)) * (x ^ 2 * (x + 4) / 4) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (2 * (x + 4) ^ 2) * (x ^ 2 * (x + 4) ^ 2) = x ^ 2 / 2 := by
    rw [one_div, show x ^ 2 * (x + 4) ^ 2 = (2 * (x + 4) ^ 2) * (x ^ 2 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e4 : 1 / (4 * x) * (x ^ 2 * (x + 4) ^ 2) = x * (x + 4) ^ 2 / 4 := by
    rw [one_div, show x ^ 2 * (x + 4) ^ 2 = (4 * x) * (x * (x + 4) ^ 2 / 4) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e5 : 1 / (2 * x ^ 2) * (x ^ 2 * (x + 4) ^ 2) = (x + 4) ^ 2 / 2 := by
    rw [one_div, show x ^ 2 * (x + 4) ^ 2 = (2 * x ^ 2) * ((x + 4) ^ 2 / 2) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, sub_mul, add_mul, add_mul, e1, e2, e3, e4, e5]; ring

private lemma hi_frac_identity (x : ℝ) (hx : 0 < x) :
    1 / (x + 4) ^ 2 + 1 / (4 * (x + 4)) - 1 / (4 * x) =
    -4 / (x * (x + 4) ^ 2) := by
  have hx4 : (0 : ℝ) < x + 4 := by linarith
  rw [eq_div_iff (by positivity : x * (x + 4) ^ 2 ≠ 0)]
  have e1 : 1 / (x + 4) ^ 2 * (x * (x + 4) ^ 2) = x := by
    rw [one_div, show x * (x + 4) ^ 2 = (x + 4) ^ 2 * x from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e2 : 1 / (4 * (x + 4)) * (x * (x + 4) ^ 2) = x * (x + 4) / 4 := by
    rw [one_div, show x * (x + 4) ^ 2 = (4 * (x + 4)) * (x * (x + 4) / 4) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  have e3 : 1 / (4 * x) * (x * (x + 4) ^ 2) = (x + 4) ^ 2 / 4 := by
    rw [one_div, show x * (x + 4) ^ 2 = (4 * x) * ((x + 4) ^ 2 / 4) from by ring,
      inv_mul_cancel_left₀ (by positivity)]
  rw [sub_mul, add_mul, e1, e2, e3]; ring

/-! ## Step differences -/

lemma S_lo_step (a N : ℕ) (ha : 0 < a) :
    S_lo a (N + 1) - S_lo a N =
      8 / ((4 * (N : ℝ) + (a : ℝ)) ^ 2 * (4 * (N : ℝ) + (a : ℝ) + 4) ^ 2) := by
  have hNa : (0 : ℝ) < 4 * (N : ℝ) + (a : ℝ) := by positivity
  show (range (N + 1)).sum (fun k => 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
      1 / (4 * (4 * ((N + 1 : ℕ) : ℝ) + (a : ℝ))) +
      1 / (2 * (4 * ((N + 1 : ℕ) : ℝ) + (a : ℝ)) ^ 2) -
    ((range N).sum (fun k => 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
      1 / (4 * (4 * (N : ℝ) + (a : ℝ))) +
      1 / (2 * (4 * (N : ℝ) + (a : ℝ)) ^ 2)) =
    8 / ((4 * (N : ℝ) + (a : ℝ)) ^ 2 * (4 * (N : ℝ) + (a : ℝ) + 4) ^ 2)
  have hcast' : 4 * ((N : ℝ) + 1) + (a : ℝ) = 4 * (N : ℝ) + (a : ℝ) + 4 := by ring
  simp only [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring, hcast']
  rw [sum_range_succ]
  -- Now the new term is 1/(4*N+a)^2, and the tail shifts from 4N+a to 4N+a+4
  linarith [lo_frac_identity (4 * (N : ℝ) + (a : ℝ)) hNa]

lemma S_hi_step (a N : ℕ) (ha : 0 < a) :
    S_hi a (N + 1) - S_hi a N =
      -4 / ((4 * (N : ℝ) + (a : ℝ)) * (4 * (N : ℝ) + (a : ℝ) + 4) ^ 2) := by
  have hNa : (0 : ℝ) < 4 * (N : ℝ) + (a : ℝ) := by positivity
  show (range (N + 1 + 1)).sum (fun k => 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
      1 / (4 * (4 * ((N + 1 : ℕ) : ℝ) + (a : ℝ))) -
    ((range (N + 1)).sum (fun k => 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
      1 / (4 * (4 * (N : ℝ) + (a : ℝ)))) =
    -4 / ((4 * (N : ℝ) + (a : ℝ)) * (4 * (N : ℝ) + (a : ℝ) + 4) ^ 2)
  simp only [show ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 from by push_cast; ring]
  rw [show N + 1 + 1 = (N + 1) + 1 from by ring, sum_range_succ]
  -- Simplify all casts of N+1 to N+1
  have hcast : 4 * ((N + 1 : ℕ) : ℝ) + (a : ℝ) = 4 * (N : ℝ) + (a : ℝ) + 4 := by push_cast; ring
  have hcast' : 4 * ((N : ℝ) + 1) + (a : ℝ) = 4 * (N : ℝ) + (a : ℝ) + 4 := by ring
  rw [hcast, hcast']
  linarith [hi_frac_identity (4 * (N : ℝ) + (a : ℝ)) hNa]

/-! ## Monotonicity -/

lemma S_lo_step_pos (a N : ℕ) (ha : 0 < a) : S_lo a N < S_lo a (N + 1) := by
  have h := S_lo_step a N ha
  have : (0 : ℝ) < 8 / ((4 * (N : ℝ) + (a : ℝ)) ^ 2 * (4 * (N : ℝ) + (a : ℝ) + 4) ^ 2) :=
    by positivity
  linarith

lemma S_hi_step_neg (a N : ℕ) (ha : 0 < a) : S_hi a (N + 1) < S_hi a N := by
  have h := S_hi_step a N ha
  have hNa : (0 : ℝ) < 4 * (N : ℝ) + (a : ℝ) := by positivity
  have : -4 / ((4 * (N : ℝ) + (a : ℝ)) * (4 * (N : ℝ) + (a : ℝ) + 4) ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

lemma S_lo_strictMono (a : ℕ) (ha : 0 < a) : StrictMono (S_lo a) :=
  strictMono_nat_of_lt_succ (fun n => S_lo_step_pos a n ha)

lemma S_hi_strictAnti (a : ℕ) (ha : 0 < a) : StrictAnti (fun N => S_hi a (N + 1)) :=
  strictAnti_nat_of_succ_lt (fun n => S_hi_step_neg a (n + 1) ha)

/-! ## Convergence -/

private lemma tendsto_inv_4Na (a : ℕ) :
    Tendsto (fun N : ℕ => 1 / (4 * (4 * (N : ℝ) + (a : ℝ)))) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    (tendsto_atTop_add_const_right _ (a : ℝ)
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) tendsto_natCast_atTop_atTop))

private lemma tendsto_inv_2Na_sq (a : ℕ) :
    Tendsto (fun N : ℕ => 1 / (2 * (4 * (N : ℝ) + (a : ℝ)) ^ 2)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    ((tendsto_pow_atTop (by omega : 2 ≠ 0)).comp
      (tendsto_atTop_add_const_right _ (a : ℝ)
        (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) tendsto_natCast_atTop_atTop)))

lemma S_lo_tendsto (a : ℕ) (ha : 0 < a) :
    Tendsto (S_lo a) atTop (𝓝 (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2)) := by
  unfold S_lo
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
      (1 / (4 * (4 * (N : ℝ) + (a : ℝ))) + 1 / (2 * (4 * (N : ℝ) + (a : ℝ)) ^ 2)))
      atTop (𝓝 (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2)) by
    exact h.congr (fun n => by ring)
  rw [show (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) =
    (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) + (0 + 0) from by ring]
  exact (tendsto_partial_sum a ha).add
    ((tendsto_inv_4Na a).add (tendsto_inv_2Na_sq a))

lemma S_hi_tendsto (a : ℕ) (ha : 0 < a) :
    Tendsto (fun N => S_hi a (N + 1)) atTop (𝓝 (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2)) := by
  unfold S_hi
  suffices h : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (N + 1 + 1), 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) +
      1 / (4 * (4 * ((N + 1 : ℕ) : ℝ) + (a : ℝ))))
      atTop (𝓝 (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2)) by
    exact h.congr (fun n => by ring)
  rw [show (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) =
    (∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2) + 0 from by ring]
  refine Tendsto.add ?_ ?_
  · -- partial sums tend to tsum
    have h := tendsto_partial_sum a ha
    exact h.comp (tendsto_add_atTop_nat 2)
  · -- correction tends to 0
    exact (tendsto_inv_4Na a).comp (tendsto_add_atTop_nat 1)

/-! ## Bounds from monotonicity + convergence -/

lemma S_lo_le (a N : ℕ) (ha : 0 < a) :
    S_lo a N ≤ ∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2 := by
  exact ge_of_tendsto (S_lo_tendsto a ha)
    (eventually_atTop.mpr ⟨N, fun k hk => (S_lo_strictMono a ha).monotone hk⟩)

lemma le_S_hi (a N : ℕ) (ha : 0 < a) :
    ∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2 ≤ S_hi a N := by
  -- S_hi a (N+1) ≤ S_hi a N from step_neg
  -- L ≤ S_hi a (N+1) from convergence of the antitone sequence
  have hle : ∑' k : ℕ, 1 / (4 * (k : ℝ) + (a : ℝ)) ^ 2 ≤ S_hi a (N + 1) := by
    -- fun m => S_hi a (m+1) is StrictAnti and tends to the tsum
    exact le_of_tendsto (S_hi_tendsto a ha)
      (eventually_atTop.mpr ⟨N, fun k hk => (S_hi_strictAnti a ha).antitone hk⟩)
  exact hle.trans (S_hi_step_neg a N ha).le

/-! ## Catalan's constant -/

/-- Catalan's constant G = Σ 1/(4k+1)² - Σ 1/(4k+3)². -/
noncomputable def catalanConstant : ℝ :=
  (∑' k : ℕ, 1 / (4 * (k : ℝ) + 1) ^ 2) - (∑' k : ℕ, 1 / (4 * (k : ℝ) + 3) ^ 2)

lemma catalan_lo_from_bounds (N : ℕ) :
    S_lo 1 N - S_hi 3 N ≤ catalanConstant := by
  unfold catalanConstant
  have h1 := S_lo_le 1 N (by norm_num)
  have h2 := le_S_hi 3 N (by norm_num)
  linarith

lemma catalan_hi_from_bounds (N : ℕ) :
    catalanConstant ≤ S_hi 1 N - S_lo 3 N := by
  unfold catalanConstant
  have h1 := le_S_hi 1 N (by norm_num)
  have h2 := S_lo_le 3 N (by norm_num)
  linarith

/-! ## Computational verification at N = 23 -/

/-- Rational lower bound: S_lo(1, 23) as a rational number. -/
def S_lo_1_q : ℚ :=
  (range 23).sum (fun k => 1 / (4 * (k : ℚ) + 1) ^ 2) +
    1 / (4 * (4 * 23 + 1)) + 1 / (2 * (4 * 23 + 1) ^ 2)

/-- Rational upper bound: S_hi(1, 23) as a rational number. -/
def S_hi_1_q : ℚ :=
  (range 24).sum (fun k => 1 / (4 * (k : ℚ) + 1) ^ 2) +
    1 / (4 * (4 * 23 + 1))

/-- Rational lower bound: S_lo(3, 23) as a rational number. -/
def S_lo_3_q : ℚ :=
  (range 23).sum (fun k => 1 / (4 * (k : ℚ) + 3) ^ 2) +
    1 / (4 * (4 * 23 + 3)) + 1 / (2 * (4 * 23 + 3) ^ 2)

/-- Rational upper bound: S_hi(3, 23) as a rational number. -/
def S_hi_3_q : ℚ :=
  (range 24).sum (fun k => 1 / (4 * (k : ℚ) + 3) ^ 2) +
    1 / (4 * (4 * 23 + 3))

-- Verify the numerical bounds
set_option maxHeartbeats 4000000 in
lemma G_lo_q_ge : S_lo_1_q - S_hi_3_q ≥ 9159 / 10000 := by
  norm_num [S_lo_1_q, S_hi_3_q, Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
lemma G_hi_q_le : S_hi_1_q - S_lo_3_q ≤ 9161 / 10000 := by
  norm_num [S_hi_1_q, S_lo_3_q, Finset.sum_range_succ]

-- Cast rational bounds to real
lemma S_lo_1_q_cast : (S_lo_1_q : ℝ) = S_lo 1 23 := by
  simp only [S_lo_1_q, S_lo]; push_cast; norm_num

lemma S_hi_1_q_cast : (S_hi_1_q : ℝ) = S_hi 1 23 := by
  simp only [S_hi_1_q, S_hi]; push_cast; norm_num

lemma S_lo_3_q_cast : (S_lo_3_q : ℝ) = S_lo 3 23 := by
  simp only [S_lo_3_q, S_lo]; push_cast; norm_num

lemma S_hi_3_q_cast : (S_hi_3_q : ℝ) = S_hi 3 23 := by
  simp only [S_hi_3_q, S_hi]; push_cast; norm_num

lemma catalan_lo_23 : (9159 : ℝ) / 10000 ≤ S_lo 1 23 - S_hi 3 23 := by
  rw [← S_lo_1_q_cast, ← S_hi_3_q_cast,
    show (9159 : ℝ) / 10000 = ((9159 / 10000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast G_lo_q_ge

lemma catalan_hi_23 : S_hi 1 23 - S_lo 3 23 ≤ (9161 : ℝ) / 10000 := by
  rw [← S_hi_1_q_cast, ← S_lo_3_q_cast,
    show (9161 : ℝ) / 10000 = ((9161 / 10000 : ℚ) : ℝ) from by push_cast; ring]
  exact_mod_cast G_hi_q_le

end CatalanBounds

open CatalanBounds in
/-- Catalan's constant is at least 0.9159. -/
theorem catalan_lo : (9159 : ℝ) / 10000 ≤ catalanConstant :=
  le_trans catalan_lo_23 (catalan_lo_from_bounds 23)

open CatalanBounds in
/-- Catalan's constant is at most 0.9161. -/
theorem catalan_hi : catalanConstant ≤ (9161 : ℝ) / 10000 :=
  le_trans (catalan_hi_from_bounds 23) catalan_hi_23


