import Playground.Lagarias.PrimeThreshold

/-!
# Existence and elementary structure of colossally abundant integers

For each positive parameter, only finitely many primes can improve the weight
at exponent zero. Choosing optimal exponents at these primes constructs a global
maximizer. Its exponents decrease with the prime, its prime support is an initial
segment, and its ordinary divisor ratio is strictly greater than that of every
smaller positive integer.

All statements here concern the actual arithmetic function `sigma`; none uses
an analytic estimate for primes or a hypothesis about the zeta function.
-/

namespace LeanEval.NumberTheory.Lagarias.Robin

open Finset
open scoped ArithmeticFunction.sigma

/-- A deliberately generous cutoff beyond which exponent zero is optimal.
The useful point is finiteness, not a sharp bound for the largest prime. -/
lemma primeIncrement_zero_le_rpow_of_large_base {p ε : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) (hcut : (2 : ℝ) ^ ε⁻¹ ≤ p) :
    primeIncrement p 0 ≤ p ^ ε := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hPow : (2 : ℝ) ≤ p ^ ε := by
    calc
      2 = ((2 : ℝ) ^ ε⁻¹) ^ ε :=
        (Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) (ne_of_gt hε)).symm
      _ ≤ p ^ ε := Real.rpow_le_rpow
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hcut hε.le
  have hInv : 1 / p ≤ 1 := by
    apply (div_le_iff₀ hp0).mpr
    simpa using hp
  rw [primeIncrement_zero]
  linarith only [hInv, hPow]

/-- Every positive real parameter has a global maximizing positive integer.
This also fixes the convention at the possible first maximizer `1`. -/
theorem exists_isColossallyAbundantFor {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, IsColossallyAbundantFor ε n := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_gt ((2 : ℝ) ^ ε⁻¹)
  let s : Finset ℕ := (range B).filter Nat.Prime
  let a : ℕ → ℕ := fun p => if hp : p.Prime then
    (exists_sigmaWeight_prime_power_maximizer hp hε).choose else 0
  have ha (p : ℕ) (hp : p.Prime) :
      ∀ k : ℕ, sigmaWeight ε (p ^ k) ≤ sigmaWeight ε (p ^ a p) := by
    dsimp only [a]
    rw [dif_pos hp]
    exact (exists_sigmaWeight_prime_power_maximizer hp hε).choose_spec
  let f : ℕ →₀ ℕ := Finsupp.onFinset s (fun p => if p ∈ s then a p else 0)
    (by intro p hp; by_contra hps; simp [hps] at hp)
  have hf_apply (p : ℕ) : f p = if p ∈ s then a p else 0 := rfl
  have hSupport : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    have hne : f p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hps : p ∈ s := by
      by_contra hps
      exact hne (by rw [hf_apply, if_neg hps])
    exact (Finset.mem_filter.mp hps).2
  let N : ℕ := f.prod (fun p k => p ^ k)
  have hN0 : N ≠ 0 := by
    change f.prod (fun p k => p ^ k) ≠ 0
    exact Finsupp.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hSupport p hp).ne_zero
  have hFact : N.factorization = f := Nat.prod_pow_factorization_eq_self hSupport
  refine ⟨N, isColossallyAbundantFor_of_primePower_maxima hε (Nat.pos_of_ne_zero hN0) ?_⟩
  intro p hp k
  by_cases hps : p ∈ s
  · have hfp : N.factorization p = a p := by rw [hFact, hf_apply, if_pos hps]
    rw [hfp]
    exact ha p hp k
  · have hpB : B ≤ p := by
      by_contra h
      exact hps (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
    have hcut : (2 : ℝ) ^ ε⁻¹ ≤ (p : ℝ) :=
      hB.le.trans (by exact_mod_cast hpB)
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hinc := primeIncrement_zero_le_rpow_of_large_base hpR hε hcut
    have hLocal : ∀ j : ℕ, sigmaWeight ε (p ^ j) ≤ sigmaWeight ε (p ^ 0) :=
      (sigmaWeight_prime_power_maximal_iff hp ε 0).mpr ⟨hinc, Or.inl rfl⟩
    have hfp : N.factorization p = 0 := by rw [hFact, hf_apply, if_neg hps]
    rw [hfp]
    exact hLocal k

/-- Exponents in the factorization of a maximizer decrease as the prime grows.
This is valid for every maximizer, including at parameter ties. -/
theorem factorization_antitone_on_primes {ε : ℝ} {n p q : ℕ}
    (h : IsColossallyAbundantFor ε n) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    n.factorization q ≤ n.factorization p := by
  have hT := (isColossallyAbundantFor_iff_thresholds.mp h).2.2
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  by_contra hbad
  have hv : n.factorization p < n.factorization q := by omega
  have hq0 : n.factorization q ≠ 0 := by omega
  have hPrev : ε ≤ primeThreshold (q : ℝ) (n.factorization q - 1) :=
    (hT q hq).2.resolve_left hq0
  have hBase : primeThreshold (q : ℝ) (n.factorization q - 1) <
      primeThreshold (p : ℝ) (n.factorization q - 1) :=
    primeThreshold_strictAnti_base _ hpR hqR (by exact_mod_cast hpq)
  have hIndex : primeThreshold (p : ℝ) (n.factorization q - 1) ≤
      primeThreshold (p : ℝ) (n.factorization p) :=
    (primeThreshold_strictAnti hpR).antitone (by omega)
  have hNext := (hT p hp).1
  linarith only [hPrev, hBase, hIndex, hNext]

/-- The prime divisors of every maximizer form an initial segment of the primes. -/
theorem prime_dvd_of_lt_prime_dvd {ε : ℝ} {n p q : ℕ}
    (h : IsColossallyAbundantFor ε n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hqdvd : q ∣ n) : p ∣ n := by
  have hqPos := hq.factorization_pos_of_dvd (Nat.ne_of_gt h.2.1) hqdvd
  have hle := factorization_antitone_on_primes h hp hq hpq
  by_contra hnot
  have hpZero := Nat.factorization_eq_zero_of_not_dvd hnot
  omega

/-- Relate the optimized weight to the ordinary divisor ratio. -/
lemma sigma_div_self_eq_sigmaWeight_mul_rpow (ε : ℝ) {n : ℕ} (hn : 0 < n) :
    ((σ 1 n : ℕ) : ℝ) / (n : ℝ) = sigmaWeight ε n * (n : ℝ) ^ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sigmaWeight_apply, Real.rpow_add hnR, Real.rpow_one]
  field_simp [ne_of_gt hnR, ne_of_gt (Real.rpow_pos_of_pos hnR ε)]

/-- Every colossally abundant integer has a strictly larger divisor ratio than
any smaller positive integer. The assertion is vacuous when the maximizer is 1. -/
theorem sigma_div_self_lt_of_lt_isColossallyAbundantFor {ε : ℝ} {m n : ℕ}
    (h : IsColossallyAbundantFor ε n) (hm : 0 < m) (hmn : m < n) :
    ((σ 1 m : ℕ) : ℝ) / (m : ℝ) < ((σ 1 n : ℕ) : ℝ) / (n : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hPow : (m : ℝ) ^ ε < (n : ℝ) ^ ε :=
    Real.rpow_lt_rpow hmR.le (by exact_mod_cast hmn) h.1
  rw [sigma_div_self_eq_sigmaWeight_mul_rpow ε hm,
    sigma_div_self_eq_sigmaWeight_mul_rpow ε h.2.1]
  calc
    sigmaWeight ε m * (m : ℝ) ^ ε ≤ sigmaWeight ε n * (m : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (h.2.2 m hm) (Real.rpow_pos_of_pos hmR ε).le
    _ < sigmaWeight ε n * (n : ℝ) ^ ε :=
      mul_lt_mul_of_pos_left hPow (sigmaWeight_pos ε h.2.1)

end LeanEval.NumberTheory.Lagarias.Robin
