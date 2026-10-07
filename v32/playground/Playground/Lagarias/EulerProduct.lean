import Playground.Lagarias.PrimePower
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact Euler products for divisor ratios

For every positive integer, `sigma(n)/n` is the product of a finite Mertens
factor and a prime-power correction. The logarithmic identities in this module
separate precisely the two terms estimated in Robin's analytic argument.
These are finite identities; no infinite product, prime number theorem, or RH
assumption is used.
-/

namespace LeanEval.NumberTheory.Lagarias.Robin

open Finset
open scoped ArithmeticFunction.sigma

/-- A normalized prime-power divisor sum, written as a finite geometric sum. -/
noncomputable def eulerFactor (p : ℝ) (k : ℕ) : ℝ := primeSum p⁻¹ k

@[simp] lemma eulerFactor_zero (p : ℝ) : eulerFactor p 0 = 1 := by
  simp [eulerFactor]

lemma primeSum_inv_eq_div {p : ℝ} (hp : p ≠ 0) (k : ℕ) :
    primeSum p⁻¹ k = primeSum p k / p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [primeSum_succ, ih, primeSum_succ_mul]
    simp only [pow_succ', inv_pow]
    field_simp [hp]
    <;> ring

lemma eulerFactor_eq_div {p : ℝ} (hp : p ≠ 0) (k : ℕ) :
    eulerFactor p k = primeSum p k / p ^ k := primeSum_inv_eq_div hp k

lemma eulerFactor_pos {p : ℝ} (hp : 0 < p) (k : ℕ) : 0 < eulerFactor p k :=
  primeSum_pos (inv_pos.mpr hp) k

lemma one_le_eulerFactor {p : ℝ} (hp : 0 < p) (k : ℕ) : 1 ≤ eulerFactor p k := by
  simpa only [eulerFactor, primeSum_zero] using
    (primeSum_strictMono (inv_pos.mpr hp)).monotone (Nat.zero_le k)

lemma eulerFactor_eq_closed {p : ℝ} (hp : 1 < p) (k : ℕ) :
    eulerFactor p k = (1 - p⁻¹ ^ (k + 1)) / (1 - p⁻¹) := by
  unfold eulerFactor primeSum
  rw [geom_sum_eq (ne_of_lt (inv_lt_one_of_one_lt₀ hp))]
  rw [show p⁻¹ ^ (k + 1) - 1 = -(1 - p⁻¹ ^ (k + 1)) by ring,
    show p⁻¹ - 1 = -(1 - p⁻¹) by ring, neg_div_neg_eq]

lemma one_sub_prime_inv_pos {p : ℝ} (hp : 1 < p) : 0 < 1 - p⁻¹ :=
  sub_pos.mpr (inv_lt_one_of_one_lt₀ hp)

lemma one_sub_prime_inv_pow_pos {p : ℝ} (hp : 1 < p) (k : ℕ) :
    0 < 1 - p⁻¹ ^ (k + 1) := by
  apply sub_pos.mpr
  exact pow_lt_one₀ (inv_nonneg.mpr (zero_lt_one.trans hp).le)
    (inv_lt_one_of_one_lt₀ hp) (Nat.succ_ne_zero k)

/-- The geometric factor is strictly smaller than the infinite geometric bound. -/
lemma eulerFactor_lt_mertensFactor {p : ℝ} (hp : 1 < p) (k : ℕ) :
    eulerFactor p k < (1 - p⁻¹)⁻¹ := by
  rw [eulerFactor_eq_closed hp]
  have ht : 0 < p⁻¹ ^ (k + 1) := pow_pos (inv_pos.mpr (zero_lt_one.trans hp)) _
  calc
    (1 - p⁻¹ ^ (k + 1)) / (1 - p⁻¹) < 1 / (1 - p⁻¹) :=
      div_lt_div_of_pos_right (by linarith only [ht]) (one_sub_prime_inv_pos hp)
    _ = (1 - p⁻¹)⁻¹ := one_div _

/-- Finite Mertens product over an explicitly specified set of integers.
Analytic applications will supply the set of primes up to a threshold. -/
noncomputable def mertensProduct (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹

/-- The exact correction from truncating the geometric factors at the actual
prime exponents of an integer. -/
noncomputable def primePowerCorrection (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1))

lemma mertensProduct_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    0 < mertensProduct s := by
  apply Finset.prod_pos
  intro p hp
  exact inv_pos.mpr (one_sub_prime_inv_pos (by exact_mod_cast (hs p hp).one_lt))

lemma primePowerCorrection_pos (n : ℕ) : 0 < primePowerCorrection n := by
  apply Finset.prod_pos
  intro p hp
  exact one_sub_prime_inv_pow_pos
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) _

lemma primePowerCorrection_le_one (n : ℕ) : primePowerCorrection n ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact (one_sub_prime_inv_pow_pos
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) _).le
  · intro p hp
    exact sub_le_self _ (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) _)

/-- Prime-power factorization of the normalized divisor sum. -/
theorem sigma_div_self_eq_prod_eulerFactor {n : ℕ} (hn : n ≠ 0) :
    ((σ 1 n : ℕ) : ℝ) / (n : ℝ) =
      ∏ p ∈ n.primeFactors, eulerFactor (p : ℝ) (n.factorization p) := by
  calc
    ((σ 1 n : ℕ) : ℝ) / (n : ℝ) = sigmaWeight 0 n := by simp [sigmaWeight_apply]
    _ = ∏ p ∈ n.primeFactors, sigmaWeight 0 (p ^ n.factorization p) :=
      sigmaWeight_eq_prod_primeFactors 0 hn
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
      rw [sigmaWeight_prime_pow hpPrime, eulerFactor_eq_div hpR]
      simp [primePowerWeight]

/-- Separate the Mertens product from the finite prime-power correction. -/
theorem sigma_div_self_eq_correction_mul_mertens {n : ℕ} (hn : n ≠ 0) :
    ((σ 1 n : ℕ) : ℝ) / (n : ℝ) =
      primePowerCorrection n * mertensProduct n.primeFactors := by
  rw [sigma_div_self_eq_prod_eulerFactor hn]
  unfold primePowerCorrection mertensProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [eulerFactor_eq_closed (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)]
  exact div_eq_mul_inv _ _

/-- The elementary Euler-product upper bound, with no asymptotic assertion. -/
theorem sigma_div_self_le_mertens {n : ℕ} (hn : n ≠ 0) :
    ((σ 1 n : ℕ) : ℝ) / (n : ℝ) ≤ mertensProduct n.primeFactors := by
  rw [sigma_div_self_eq_correction_mul_mertens hn]
  have hpos : 0 < mertensProduct n.primeFactors :=
    mertensProduct_pos fun _ hp => Nat.prime_of_mem_primeFactors hp
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (primePowerCorrection_le_one n) hpos.le

lemma log_mertensProduct {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Real.log (mertensProduct s) = -∑ p ∈ s, Real.log (1 - (p : ℝ)⁻¹) := by
  unfold mertensProduct
  rw [Real.log_prod (fun p hp => ne_of_gt (inv_pos.mpr
    (one_sub_prime_inv_pos (by exact_mod_cast (hs p hp).one_lt))))]
  simp only [Real.log_inv, Finset.sum_neg_distrib]

lemma log_primePowerCorrection (n : ℕ) :
    Real.log (primePowerCorrection n) =
      ∑ p ∈ n.primeFactors, Real.log (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1)) := by
  unfold primePowerCorrection
  exact Real.log_prod fun p hp => ne_of_gt (one_sub_prime_inv_pow_pos
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) _)

/-- Logarithmic divisor-ratio identity, exposing the two separate prime sums. -/
theorem log_sigma_div_self_eq {n : ℕ} (hn : n ≠ 0) :
    Real.log (((σ 1 n : ℕ) : ℝ) / (n : ℝ)) =
      (∑ p ∈ n.primeFactors, Real.log (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1))) -
        ∑ p ∈ n.primeFactors, Real.log (1 - (p : ℝ)⁻¹) := by
  rw [sigma_div_self_eq_correction_mul_mertens hn,
    Real.log_mul (ne_of_gt (primePowerCorrection_pos n))
      (ne_of_gt (mertensProduct_pos fun _ hp => Nat.prime_of_mem_primeFactors hp)),
    log_primePowerCorrection, log_mertensProduct (fun _ hp => Nat.prime_of_mem_primeFactors hp)]
  ring

/-- The logarithm of an integer as the exponent-weighted sum over its primes. -/
theorem log_nat_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  have hN : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa only [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn
  have hNR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast hN.symm
  rw [hNR, Real.log_prod (fun p hp => pow_ne_zero _
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
  simp only [Real.log_pow]

end LeanEval.NumberTheory.Lagarias.Robin
