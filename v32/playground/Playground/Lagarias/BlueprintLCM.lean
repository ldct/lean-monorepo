import Playground.Lagarias.BlueprintLocalFactor
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.PSeries

/-!
# Least common multiples and prime-power logarithms

Blueprint: Section 9, especially Lemma 9.1. The constant 6 and the real-variable
cutoff 4 are retained. Only elementary finite prime products and a telescoping
bound for reciprocal squares are used; no prime number theorem enters.

`B` is the prime-power sum (3.3), represented by grouping the powers at each
prime. Its equality to the von Mangoldt form, its asymptotics, and the integral
representation of the smoothed error are separate obligations.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset
open scoped ArithmeticFunction.sigma

/-- Largest exponent with `p^k <= x`, for prime `p` and `x >= 1`. -/
noncomputable def K (p : ℕ) (x : ℝ) : ℕ := Nat.log p ⌊x⌋₊

/-- The exact prime-power logarithm `B(x)` of (3.3), grouped by prime. -/
noncomputable def B (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, primeLogPartial (p : ℝ) (K p x)

/-- `lcm(1,...,floor(x))`, including its ordinary natural-number value. -/
noncomputable def lcmSeq (x : ℝ) : ℕ := Nat.lcmUpto ⌊x⌋₊

lemma lcmSeq_pos (x : ℝ) : 0 < lcmSeq x := Nat.lcmUpto_pos _

lemma log_lcmSeq (x : ℝ) : Real.log (lcmSeq x : ℝ) = Chebyshev.psi x := by
  rw [lcmSeq, ← Chebyshev.psi_eq_log_lcmUpto]
  exact (Chebyshev.psi_eq_psi_coe_floor x).symm

lemma K_pos {p : ℕ} {x : ℝ} (hp : p ∈ Nat.primesLE ⌊x⌋₊) : 1 ≤ K p x := by
  apply Nat.le_log_of_pow_le (Nat.prime_of_mem_primesLE hp).one_lt
  simpa using Nat.le_of_mem_primesLE hp

lemma pow_K_succ_gt {p : ℕ} (hp : p.Prime) (x : ℝ) :
    x < (p : ℝ) ^ (K p x + 1) := by
  have hn : ⌊x⌋₊ < p ^ (K p x + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
  have hR := Nat.lt_of_floor_lt hn
  exact_mod_cast hR

lemma inv_pow_K_succ_le_inv {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 0 < x) :
    (p : ℝ)⁻¹ ^ (K p x + 1) ≤ 1 / x := by
  simpa only [one_div, inv_pow] using
    one_div_le_one_div_of_le hx (pow_K_succ_gt hp x).le

lemma inv_pow_K_succ_le_inv_sq {p : ℕ} {x : ℝ}
    (hp : p ∈ Nat.primesLE ⌊x⌋₊) : (p : ℝ)⁻¹ ^ (K p x + 1) ≤ ((p : ℝ) ^ 2)⁻¹ := by
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  have hq1 : (p : ℝ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hpR).le
  have hk := K_pos hp
  rw [show K p x + 1 = 2 + (K p x - 1) by omega, pow_add, ← inv_pow]
  exact mul_le_of_le_one_right (pow_nonneg hq0 _) (pow_le_one₀ hq0 hq1)

lemma sqrt_ge_two {x : ℝ} (hx : 4 ≤ x) : 2 ≤ Real.sqrt x := by
  have hnonneg := Real.sqrt_nonneg x
  have hs := Real.sq_sqrt (by linarith : 0 ≤ x)
  nlinarith

/-- The small-prime part of the correction, bounded by counting integers. -/
lemma small_prime_correction_le {x : ℝ} (hx : 4 ≤ x) :
    (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => (p : ℝ) ≤ Real.sqrt x),
      (p : ℝ)⁻¹ ^ (K p x + 1)) ≤ 1 / Real.sqrt x := by
  classical
  let S := (Nat.primesLE ⌊x⌋₊).filter (fun p => (p : ℝ) ≤ Real.sqrt x)
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := by linarith [sqrt_ge_two hx]
  have hsub : S ⊆ Finset.Ioc 0 ⌊Real.sqrt x⌋₊ := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hp'.1).pos,
      (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr hp'.2⟩
  have hcard : S.card ≤ ⌊Real.sqrt x⌋₊ := by
    simpa using Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ Real.sqrt x :=
    (by exact_mod_cast hcard).trans (Nat.floor_le (Real.sqrt_nonneg x))
  calc
    (∑ p ∈ S, (p : ℝ)⁻¹ ^ (K p x + 1)) ≤ ∑ _p ∈ S, (1 / x) := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_pow_K_succ_le_inv (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1) hx0
    _ = (S.card : ℝ) / x := by simp [div_eq_mul_inv]
    _ ≤ Real.sqrt x / x := div_le_div_of_nonneg_right hcardR hx0.le
    _ = 1 / Real.sqrt x := by
      rw [← Real.sq_sqrt hx0.le]
      field_simp

/-- The large-prime part is dominated by all reciprocal squares above sqrt(x). -/
lemma large_prime_correction_le {x : ℝ} (hx : 4 ≤ x) :
    (∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬(p : ℝ) ≤ Real.sqrt x),
      (p : ℝ)⁻¹ ^ (K p x + 1)) ≤ 2 / Real.sqrt x := by
  classical
  let S := (Nat.primesLE ⌊x⌋₊).filter (fun p => ¬(p : ℝ) ≤ Real.sqrt x)
  let m : ℕ := ⌊Real.sqrt x⌋₊
  have hs2 := sqrt_ge_two hx
  have hs0 : 0 < Real.sqrt x := by linarith
  have hm : 0 < m := by
    apply Nat.lt_of_lt_of_le (by norm_num : 0 < 1)
    exact (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr (by linarith)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hhalf : Real.sqrt x / 2 ≤ (m : ℝ) := by
    have ht := Nat.lt_floor_add_one (Real.sqrt x)
    change Real.sqrt x < (m : ℝ) + 1 at ht
    linarith
  have hsub : S ⊆ Finset.Ioc m (max m ⌊x⌋₊) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hmp : (m : ℝ) < p :=
      (Nat.floor_le (Real.sqrt_nonneg x)).trans_lt (lt_of_not_ge hp'.2)
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hmp,
      (Nat.le_of_mem_primesLE hp'.1).trans (le_max_right _ _)⟩
  calc
    (∑ p ∈ S, (p : ℝ)⁻¹ ^ (K p x + 1)) ≤ ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_pow_K_succ_le_inv_sq (Finset.mem_filter.mp hp).1
    _ ≤ ∑ p ∈ Finset.Ioc m (max m ⌊x⌋₊), ((p : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ (m : ℝ)⁻¹ - (max m ⌊x⌋₊ : ℕ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (Nat.ne_of_gt hm) (le_max_left _ _)
    _ ≤ (m : ℝ)⁻¹ := sub_le_self _ (by positivity)
    _ ≤ 2 / Real.sqrt x := by
      have hh := one_div_le_one_div_of_le (half_pos hs0) hhalf
      simpa [one_div, div_eq_mul_inv, mul_comm] using hh

/-- The elementary reciprocal-prime-power correction has order at most x^(-1/2). -/
theorem sum_prime_power_correction_le {x : ℝ} (hx : 4 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ ^ (K p x + 1)) ≤ 3 / Real.sqrt x := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => (p : ℝ) ≤ Real.sqrt x)]
  have hs := small_prime_correction_le hx
  have hl := large_prime_correction_le hx
  linarith

/-- The exact finite identity preceding Lemma 9.1. -/
lemma log_sigma_lcmSeq_eq (x : ℝ) :
    Real.log (((σ 1 (lcmSeq x) : ℕ) : ℝ) / (lcmSeq x : ℝ)) =
      B x - ∑ p ∈ Nat.primesLE ⌊x⌋₊, primeLogLoss (p : ℝ) (K p x) := by
  have hprod := Robin.sigma_div_self_eq_prod_eulerFactor (Nat.ne_of_gt (lcmSeq_pos x))
  have hexp (p : ℕ) (hp : p ∈ Nat.primesLE ⌊x⌋₊) :
      (lcmSeq x).factorization p = K p x :=
    Nat.factorization_lcmUpto _ (Nat.prime_of_mem_primesLE hp)
  rw [hprod]
  unfold lcmSeq
  rw [Nat.primeFactors_lcmUpto, Real.log_prod (fun p hp =>
    (Robin.eulerFactor_pos (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos) _).ne')]
  unfold B
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  change Real.log (Robin.eulerFactor (p : ℝ) ((lcmSeq x).factorization p)) = _
  rw [hexp p hp]
  unfold primeLogLoss
  ring

/-- Blueprint Lemma 9.1, including the exact constant and real cutoff. -/
theorem log_sigma_lcmSeq_ge {x : ℝ} (hx : 4 ≤ x) :
    B x - 6 / Real.sqrt x ≤
      Real.log (((σ 1 (lcmSeq x) : ℕ) : ℝ) / (lcmSeq x : ℝ)) := by
  rw [log_sigma_lcmSeq_eq]
  have hloss : (∑ p ∈ Nat.primesLE ⌊x⌋₊, primeLogLoss (p : ℝ) (K p x)) ≤
      2 * ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹ ^ (K p x + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    exact primeLogLoss_le_two_mul (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le) _
  have hsum := sum_prime_power_correction_le hx
  linarith

end LeanEval.NumberTheory.Lagarias.Blueprint
