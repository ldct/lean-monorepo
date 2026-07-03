import Mathlib

/-!
# The integral ∫₀¹ {1/x} dx = 1 - γ

This file formalizes the classical computation showing that
the integral of the fractional part of `1/x` over `(0, 1]` equals
`1 - γ`, where `γ` is the Euler–Mascheroni constant.

The argument decomposes the interval `(0, 1]` into the pieces
`(1/(n+1), 1/n]` (for `n ≥ 1`), evaluates the elementary integral
on each piece, and then identifies the resulting series with
`1 - γ` via telescoping the harmonic and logarithmic sums.
-/

open Real Set MeasureTheory Filter Topology Finset intervalIntegral
open scoped NNReal ENNReal

namespace FracPartIntegral

/-- On the half-open interval `(1/(n+1), 1/n]`, the fractional part of
`1/x` equals `1/x - n`. -/
lemma fract_inv_eq_of_mem
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx₁ : 1 / (n + 1 : ℝ) < x) (hx₂ : x ≤ 1 / n) :
    Int.fract (1 / x) = 1 / x - n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hxpos : 0 < x := by
    have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact h0.trans hx₁
  -- We want ⌊1/x⌋ = n
  have hfloor : ⌊(1 / x : ℝ)⌋ = (n : ℤ) := by
    apply (Int.floor_eq_iff (z := (n : ℤ))).mpr
    refine ⟨?_, ?_⟩
    · -- n ≤ 1/x : from x ≤ 1/n
      rw [Int.cast_natCast, le_div_iff₀ hxpos]
      have hxn : x * (n : ℝ) ≤ 1 := by
        have h1 : x ≤ 1 / (n : ℝ) := hx₂
        have := mul_le_mul_of_nonneg_right h1 hnpos.le
        rwa [one_div, inv_mul_cancel₀ hnpos.ne'] at this
      linarith
    · -- 1/x < n + 1 : from 1/(n+1) < x
      push_cast
      rw [div_lt_iff₀ hxpos]
      have hxn1 : 1 < x * ((n : ℝ) + 1) := by
        have h1 : 1 / ((n : ℝ) + 1) < x := hx₁
        have := mul_lt_mul_of_pos_right h1 hn1pos
        rwa [one_div, inv_mul_cancel₀ hn1pos.ne'] at this
      linarith
  unfold Int.fract
  rw [hfloor]
  push_cast
  ring

/-- Closed form of the integral on a single piece `[1/(n+1), 1/n]`. -/
lemma integral_piece (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (1 / (n + 1 : ℝ))..(1 / n), Int.fract (1 / x) =
      Real.log ((n + 1 : ℝ) / n) - 1 / (n + 1 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h_inv1_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have h_inv2_pos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hle : (1 / ((n : ℝ) + 1)) ≤ (1 / (n : ℝ)) := by
    apply one_div_le_one_div_of_le hnpos
    linarith
  -- Step 1: rewrite the integrand on the interval using fract_inv_eq_of_mem
  have heq : ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), Int.fract (1 / x) =
      ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), (1 / x - (n : ℝ)) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    obtain ⟨hx₁, hx₂⟩ := hx
    exact fract_inv_eq_of_mem hn hx₁ hx₂
  rw [heq]
  -- Step 2: split and integrate
  have h_int_inv : ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), (1 / x : ℝ) =
      Real.log ((1 / (n : ℝ)) / (1 / ((n : ℝ) + 1))) := by
    apply integral_one_div_of_pos h_inv1_pos h_inv2_pos
  have h_int_const : ∫ _ in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), ((n : ℝ)) =
      (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) * (n : ℝ) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have h_intble1 : IntervalIntegrable (fun x : ℝ => 1 / x) MeasureTheory.volume
      (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    have : 0 < x := lt_of_lt_of_le h_inv1_pos hx.1
    exact this.ne'
  have h_intble2 : IntervalIntegrable (fun _ : ℝ => (n : ℝ)) MeasureTheory.volume
      (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) := intervalIntegral.intervalIntegrable_const
  rw [intervalIntegral.integral_sub h_intble1 h_intble2, h_int_inv, h_int_const]
  -- Now simplify: log((1/n)/(1/(n+1))) = log((n+1)/n) and the constant part.
  have h1 : (1 / (n : ℝ)) / (1 / ((n : ℝ) + 1)) = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp
  rw [h1]
  have h2 : (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) * (n : ℝ) = 1 / ((n : ℝ) + 1) := by
    field_simp
    ring
  rw [h2]

/-- The integrand `λ x, {1/x}` is integrable on `(0, 1]`. -/
lemma integrableOn_fract_inv :
    IntegrableOn (fun x : ℝ => Int.fract (1 / x)) (Ioc (0 : ℝ) 1) := by
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · -- AEStronglyMeasurable
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.div measurable_id).fract
  · -- Bound
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Int.abs_fract]
    exact (Int.fract_lt_one _).le

/-- Decomposition of the integral over `(0,1]` as the sum of integrals
over the dyadic-style pieces `(1/(n+1), 1/n]`. -/
lemma integral_eq_tsum :
    ∫ x in Ioc (0 : ℝ) 1, Int.fract (1 / x) =
      ∑' n : {n : ℕ // 1 ≤ n},
        ∫ x in (1 / ((n.1 : ℝ) + 1))..(1 / (n.1 : ℝ)),
            Int.fract (1 / x) := by
  -- Define the family of pieces
  let s : {n : ℕ // 1 ≤ n} → Set ℝ :=
    fun n => Set.Ioc (1 / ((n.1 : ℝ) + 1)) (1 / (n.1 : ℝ))
  -- Step 1: Show (0, 1] = ⋃ n, s n
  have h_union : Set.Ioc (0 : ℝ) 1 = ⋃ n : {n : ℕ // 1 ≤ n}, s n := by
    ext x
    simp only [Set.mem_Ioc, Set.mem_iUnion, s]
    constructor
    · rintro ⟨hx0, hx1⟩
      -- For x ∈ (0, 1], take n = ⌊1/x⌋. Then n ≥ 1 and x ∈ (1/(n+1), 1/n].
      have hinv_pos : 0 < 1 / x := by positivity
      have hinv_ge_one : 1 ≤ 1 / x := by
        rw [le_div_iff₀ hx0]; linarith
      set m : ℕ := ⌊(1 / x : ℝ)⌋.toNat with hm_def
      have hm_pos : 1 ≤ m := by
        have : 1 ≤ ⌊(1 / x : ℝ)⌋ := Int.le_floor.mpr (by exact_mod_cast hinv_ge_one)
        rw [hm_def]
        omega
      have hfloor_eq : (m : ℤ) = ⌊(1 / x : ℝ)⌋ := by
        rw [hm_def]
        have : 0 ≤ ⌊(1 / x : ℝ)⌋ := by
          have : (1 : ℤ) ≤ ⌊(1 / x : ℝ)⌋ := Int.le_floor.mpr (by exact_mod_cast hinv_ge_one)
          omega
        omega
      refine ⟨⟨m, hm_pos⟩, ?_, ?_⟩
      · -- 1/(m+1) < x : equivalent to 1/x < m+1 (for x > 0).
        -- Since ⌊1/x⌋ = m, we have 1/x < m+1.
        have h1 : (1 / x : ℝ) < (m : ℝ) + 1 := by
          have := Int.lt_floor_add_one (1 / x : ℝ)
          rw [← hfloor_eq] at this
          exact_mod_cast this
        have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        rw [div_lt_iff₀ hm1pos]
        rw [div_lt_iff₀ hx0] at h1
        linarith
      · -- x ≤ 1/m : equivalent to m ≤ 1/x. Since m = ⌊1/x⌋ ≤ 1/x.
        have h1 : ((m : ℤ) : ℝ) ≤ (1 / x : ℝ) := by
          rw [hfloor_eq]
          exact Int.floor_le _
        have hmpos : (0 : ℝ) < (m : ℝ) := by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
          linarith
        rw [le_div_iff₀ hmpos]
        push_cast at h1
        rw [le_div_iff₀ hx0] at h1
        linarith
    · rintro ⟨⟨n, hn⟩, hx1, hx2⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h_inv1_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      refine ⟨lt_of_lt_of_le h_inv1_pos hx1.le, ?_⟩
      have : x ≤ 1 / (n : ℝ) := hx2
      have h1n_le_one : (1 : ℝ) / n ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast hn
      linarith
  -- Step 2: each s n is measurable
  have h_meas : ∀ n : {n : ℕ // 1 ≤ n}, MeasurableSet (s n) := by
    intro n
    exact measurableSet_Ioc
  -- Step 3: pairwise disjoint
  have h_disj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    simp only [Function.onFun, s]
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hij' : i ≠ j := by simpa using hij
    -- WLOG i < j; then 1/i ≤ 1/(j+1) doesn't hold actually; the intervals are nested
    -- by reciprocal. If i < j then 1/(j+1) < 1/(i+1) and 1/j < 1/i, so the intervals are
    -- disjoint because Ioc(1/(j+1), 1/j) is entirely below 1/(i+1) when j ≥ i+1, i.e. 1/j ≤ 1/(i+1).
    rcases lt_or_gt_of_ne hij' with h | h
    · -- i < j, so j ≥ i+1, so 1/j ≤ 1/(i+1)
      apply Set.disjoint_iff_forall_ne.mpr
      intros x hx y hy hxy
      subst hxy
      simp only [Set.mem_Ioc] at hx hy
      have hi_pos : (0 : ℝ) < i := by exact_mod_cast hi
      have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj
      have hij_le : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      have hi1_pos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have h_le : (1 : ℝ) / (j : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hi1_pos hij_le
      -- hx : 1/(i+1) < x ∧ x ≤ 1/i; hy : 1/(j+1) < x ∧ x ≤ 1/j.
      -- x ≤ 1/j ≤ 1/(i+1) < x, contradiction.
      linarith [hx.1, hy.2]
    · -- i > j, symmetric
      apply Set.disjoint_iff_forall_ne.mpr
      intros x hx y hy hxy
      subst hxy
      simp only [Set.mem_Ioc] at hx hy
      have hi_pos : (0 : ℝ) < i := by exact_mod_cast hi
      have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj
      have hji_le : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h_le : (1 : ℝ) / (i : ℝ) ≤ 1 / ((j : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hj1_pos hji_le
      linarith [hx.2, hy.1]
  -- Step 4: Use integral_iUnion
  rw [h_union]
  have h_int : IntegrableOn (fun x : ℝ => Int.fract (1 / x)) (⋃ n, s n) := by
    rw [← h_union]
    exact integrableOn_fract_inv
  rw [MeasureTheory.integral_iUnion h_meas h_disj h_int]
  -- Step 5: convert each set integral to interval integral
  apply tsum_congr
  intro n
  rcases n with ⟨n, hn⟩
  simp only [s]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : (1 / ((n : ℝ) + 1)) ≤ (1 / (n : ℝ)) := by
    apply one_div_le_one_div_of_le hnpos
    linarith
  rw [intervalIntegral.integral_of_le hle]

/-- The partial sum identity used after telescoping the product
`∏_{n=1}^{N} (n+1)/n = N+1`. -/
lemma partial_sum_eq (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N,
        (Real.log (((n : ℝ) + 1) / n) - 1 / ((n : ℝ) + 1)) =
      Real.log (N + 1 : ℝ) -
        (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k) + 1 := by
  -- Split the sum
  rw [Finset.sum_sub_distrib]
  -- The log telescoping part
  have hlog : ∑ n ∈ Finset.Icc 1 N, Real.log (((n : ℝ) + 1) / n) =
      Real.log (N + 1 : ℝ) := by
    induction N, hN using Nat.le_induction with
    | base =>
      simp [Finset.Icc_self]
    | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      rw [ih]
      push_cast
      have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by
        have : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
        linarith
      have hMpos2 : (0 : ℝ) < ((M : ℝ) + 1 + 1) := by linarith
      have hne1 : ((M : ℝ) + 1) ≠ 0 := hMpos.ne'
      have hne2 : (((M : ℝ) + 1 + 1) / ((M : ℝ) + 1)) ≠ 0 := by
        apply div_ne_zero hMpos2.ne' hne1
      rw [← Real.log_mul hne1 hne2]
      congr 1
      field_simp
  rw [hlog]
  -- The 1/(n+1) part: re-index from n+1 to k
  have hsum : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) + 1) =
      (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k) - 1 := by
    -- Use shift: ∑ n ∈ Icc 1 N, f(n+1) = ∑ k ∈ Icc 2 (N+1), f(k)
    have h_shift : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) + 1) =
        ∑ k ∈ Finset.Icc 2 (N + 1), (1 : ℝ) / (k : ℝ) := by
      rw [show (Finset.Icc 2 (N + 1)) = (Finset.Icc 1 N).image (· + 1) by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨x - 1, ⟨?_, ?_⟩, ?_⟩ <;> omega
        · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
          exact ⟨by omega, by omega⟩]
      rw [Finset.sum_image (fun a _ b _ h => by omega)]
      apply Finset.sum_congr rfl
      intros n _
      push_cast
      ring
    rw [h_shift]
    -- Now: Icc 1 (N+1) = {1} ∪ Icc 2 (N+1)
    have h_split : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h_split]
    rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    simp only [Nat.cast_one, div_one]
    ring
  rw [hsum]
  ring

/-- The Euler–Mascheroni constant is the limit of `H_N - log N`. -/
lemma tendsto_harmonic_sub_log :
    Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k) - Real.log N)
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := Real.tendsto_harmonic_sub_log
  apply h.congr
  intro N
  congr 1
  rw [harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intros i _
  rw [one_div]

/-- **Main theorem.** The integral of the fractional part of `1/x` on
`(0, 1]` equals `1 − γ`, where `γ` is the Euler–Mascheroni constant. -/
theorem integral_fract_inv_eq_one_sub_gamma :
    ∫ x in Ioc (0 : ℝ) 1, Int.fract (1 / x) =
      1 - Real.eulerMascheroniConstant := by
  rw [integral_eq_tsum]
  -- Define g : ℕ → ℝ as the integrand for the (n+1)-th piece
  set g : ℕ → ℝ := fun n => ∫ x in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)),
      Int.fract (1 / x) with hg_def
  -- The closed form on each piece via integral_piece for n+1
  have hg_form : ∀ n : ℕ, g n = Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) -
      1 / ((n : ℝ) + 2) := by
    intro n
    have h := integral_piece (n + 1) (by omega)
    change ∫ x in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), Int.fract (1 / x) = _
    have e1 : ((n : ℝ) + 2) = (((n + 1 : ℕ) : ℝ) + 1) := by push_cast; ring
    have e2 : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2]
    rw [h]
  -- Each g n is non-negative
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    have hle : (1 / ((n : ℝ) + 2)) ≤ (1 / ((n : ℝ) + 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    change 0 ≤ ∫ x in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), Int.fract (1 / x)
    rw [intervalIntegral.integral_of_le hle]
    apply MeasureTheory.integral_nonneg
    intro x
    exact Int.fract_nonneg _
  -- Equivalence between {n // 1 ≤ n} and ℕ (n+1 ↔ n)
  have h_equiv : (∑' n : {n : ℕ // 1 ≤ n},
      ∫ x in (1 / ((n.1 : ℝ) + 1))..(1 / (n.1 : ℝ)), Int.fract (1 / x)) =
      ∑' n : ℕ, g n := by
    let e : ℕ ≃ {n : ℕ // 1 ≤ n} :=
      { toFun := fun n => ⟨n + 1, by omega⟩
        invFun := fun n => n.1 - 1
        left_inv := fun n => by simp
        right_inv := fun ⟨n, hn⟩ => by
          simp only [Subtype.mk.injEq]
          omega }
    rw [← Equiv.tsum_eq e]
    apply tsum_congr
    intro n
    change ∫ x in (1 / (((n + 1 : ℕ) : ℝ) + 1))..(1 / ((n + 1 : ℕ) : ℝ)), Int.fract (1 / x) =
        ∫ x in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), Int.fract (1 / x)
    have e1 : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := by push_cast; ring
    rw [e1, e2]
  rw [h_equiv]
  -- Now: ∑' n, g n = 1 - γ. Show via partial sums.
  have h_sum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g n)
      atTop (𝓝 (1 - Real.eulerMascheroniConstant)) := by
    -- The partial sum ∑_{n=0}^{N-1} g n = ∑_{n=1}^{N} g_old n where
    -- g_old n = log((n+1)/n) - 1/(n+1). Apply partial_sum_eq.
    have h_partial : ∀ N : ℕ, 1 ≤ N →
        ∑ n ∈ Finset.range N, g n =
        Real.log (N + 1 : ℝ) -
          (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k) + 1 := by
      intro N hN
      have h1 : ∑ n ∈ Finset.range N, g n =
          ∑ n ∈ Finset.Icc 1 N,
            (Real.log (((n : ℝ) + 1) / n) - 1 / ((n : ℝ) + 1)) := by
        rw [show (Finset.Icc 1 N) = (Finset.range N).image (· + 1) by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨x - 1, by omega, by omega⟩
          · rintro ⟨a, ha, rfl⟩
            exact ⟨by omega, by omega⟩]
        rw [Finset.sum_image (fun a _ b _ h => by omega)]
        apply Finset.sum_congr rfl
        intros n _
        rw [hg_form]
        push_cast
        congr 2 <;> ring
      rw [h1, partial_sum_eq N hN]
    -- Show by congruence on eventually equal functions
    have h_eq : ∀ᶠ N in (atTop : Filter ℕ), ∑ n ∈ Finset.range N, g n =
        Real.log ((N : ℝ) + 1) -
          (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k) + 1 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN using h_partial N hN
    apply Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eq)
    -- Show: tendsto (fun N => log(N+1) - H_{N+1} + 1) atTop (𝓝 (1 - γ))
    have h_target : Tendsto
        (fun N : ℕ => (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k) - Real.log ((N : ℝ) + 1))
        atTop (𝓝 Real.eulerMascheroniConstant) := by
      have h := tendsto_harmonic_sub_log
      have h2 := h.comp (Filter.tendsto_add_atTop_nat 1)
      apply h2.congr
      intro N
      simp [Function.comp]
    have h_target' :
        Tendsto (fun N : ℕ =>
          Real.log ((N : ℝ) + 1) -
            (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k) + 1)
        atTop (𝓝 (1 - Real.eulerMascheroniConstant)) := by
      have h := h_target.neg.add_const 1
      have heq : (1 - Real.eulerMascheroniConstant) = -Real.eulerMascheroniConstant + 1 := by ring
      rw [heq]
      apply h.congr
      intro N
      ring
    exact h_target'
  -- Combine
  exact ((hasSum_iff_tendsto_nat_of_nonneg hg_nonneg _).mpr h_sum).tsum_eq

end FracPartIntegral
