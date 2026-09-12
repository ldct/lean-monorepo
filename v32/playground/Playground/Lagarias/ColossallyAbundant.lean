import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Prime-power optimization for colossally abundant numbers

The arithmetic reduction used in Robin's argument: maximization of
`sigma(n) / n^(1+epsilon)` is equivalent to maximization of each prime-power
factor. No analytic estimate, RH assumption, or asymptotic result is used here.

Reference for the mathematical organization: Caveney, Nicolas and Sondow,
*On SA, CA, and GA numbers*, arXiv:1112.6010, Section 2.
-/

namespace LeanEval.NumberTheory.Lagarias.Robin

open Finset
open scoped ArithmeticFunction.sigma

/-- The multiplicative weight optimized by colossally abundant integers.
Multiplication of its values is ordinary real multiplication, not Dirichlet
convolution. Its value at zero is zero, for every real parameter. -/
noncomputable def sigmaWeight (ε : ℝ) : ArithmeticFunction ℝ where
  toFun n := ((σ 1 n : ℕ) : ℝ) / (n : ℝ) ^ (1 + ε)
  map_zero' := by simp

lemma sigmaWeight_apply (ε : ℝ) (n : ℕ) :
    sigmaWeight ε n = ((σ 1 n : ℕ) : ℝ) / (n : ℝ) ^ (1 + ε) := rfl

@[simp] lemma sigmaWeight_one (ε : ℝ) : sigmaWeight ε 1 = 1 := by
  simp [sigmaWeight_apply]

lemma sigmaWeight_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ sigmaWeight ε n := by
  exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma sigmaWeight_pos (ε : ℝ) {n : ℕ} (hn : 0 < n) : 0 < sigmaWeight ε n := by
  have hSigma : (0 : ℝ) < ((σ 1 n : ℕ) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n (Nat.ne_of_gt hn)
  exact div_pos hSigma (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

lemma sigmaWeight_mul (ε : ℝ) {m n : ℕ} (h : m.Coprime n) :
    sigmaWeight ε (m * n) = sigmaWeight ε m * sigmaWeight ε n := by
  simp only [sigmaWeight_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), div_mul_div_comm]

lemma isMultiplicative_sigmaWeight (ε : ℝ) :
    ArithmeticFunction.IsMultiplicative (sigmaWeight ε) :=
  ⟨sigmaWeight_one ε, fun h => sigmaWeight_mul ε h⟩

/-- Extend the prime-factor product to any finite superset; added primes
contribute the value at exponent zero, namely one. -/
lemma sigmaWeight_eq_prod_of_primeFactors_subset (ε : ℝ) {n : ℕ}
    (hn : n ≠ 0) {s : Finset ℕ} (hs : n.primeFactors ⊆ s) :
    sigmaWeight ε n = ∏ p ∈ s, sigmaWeight ε (p ^ n.factorization p) := by
  rw [(isMultiplicative_sigmaWeight ε).multiplicative_factorization _ hn]
  exact Finsupp.prod_of_support_subset _
    (by simpa only [Nat.support_factorization] using hs) _ (by intro p hp; simp)

lemma sigmaWeight_eq_prod_primeFactors (ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    sigmaWeight ε n = ∏ p ∈ n.primeFactors, sigmaWeight ε (p ^ n.factorization p) :=
  sigmaWeight_eq_prod_of_primeFactors_subset ε hn (Finset.Subset.refl _)

/-- A positive integer maximizing the weight at a specified positive parameter.
Including the competitor `1` makes the convention at the first maximizer explicit. -/
def IsColossallyAbundantFor (ε : ℝ) (n : ℕ) : Prop :=
  0 < ε ∧ 0 < n ∧ ∀ m : ℕ, 0 < m → sigmaWeight ε m ≤ sigmaWeight ε n

/-- Independently optimal prime-power exponents give a global maximum. -/
theorem isColossallyAbundantFor_of_primePower_maxima {ε : ℝ} {n : ℕ}
    (hε : 0 < ε) (hn : 0 < n)
    (hLocal : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      sigmaWeight ε (p ^ k) ≤ sigmaWeight ε (p ^ n.factorization p)) :
    IsColossallyAbundantFor ε n := by
  refine ⟨hε, hn, ?_⟩
  intro m hm
  rw [sigmaWeight_eq_prod_of_primeFactors_subset ε (Nat.ne_of_gt hm)
      (Finset.subset_union_left : m.primeFactors ⊆ m.primeFactors ∪ n.primeFactors),
    sigmaWeight_eq_prod_of_primeFactors_subset ε (Nat.ne_of_gt hn)
      (Finset.subset_union_right : n.primeFactors ⊆ m.primeFactors ∪ n.primeFactors)]
  apply Finset.prod_le_prod
  · intro p hp
    exact sigmaWeight_nonneg ε _
  · intro p hp
    have hPrime : p.Prime := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    exact hLocal p hPrime (m.factorization p)

/-- A global maximizer must maximize the factor at each individual prime.
The competing integer replaces only that prime's exponent. -/
theorem primePower_le_of_isColossallyAbundantFor {ε : ℝ} {n : ℕ}
    (h : IsColossallyAbundantFor ε n) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigmaWeight ε (p ^ k) ≤ sigmaWeight ε (p ^ n.factorization p) := by
  let q := n / p ^ n.factorization p
  have hDecomp : p ^ n.factorization p * q = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hq : 0 < q := by
    by_contra hq
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    rw [hq0, mul_zero] at hDecomp
    exact (Nat.ne_of_gt h.2.1) hDecomp.symm
  have hCoprime : p.Coprime q := Nat.coprime_ordCompl hp (Nat.ne_of_gt h.2.1)
  have hWeight : sigmaWeight ε n =
      sigmaWeight ε (p ^ n.factorization p) * sigmaWeight ε q := by
    calc
      sigmaWeight ε n = sigmaWeight ε (p ^ n.factorization p * q) :=
        congrArg (sigmaWeight ε) hDecomp.symm
      _ = _ := sigmaWeight_mul ε (hCoprime.pow_left _)
  have hCompare := h.2.2 (p ^ k * q) (Nat.mul_pos (pow_pos hp.pos _) hq)
  rw [sigmaWeight_mul ε (hCoprime.pow_left k), hWeight] at hCompare
  exact (mul_le_mul_iff_of_pos_right (sigmaWeight_pos ε hq)).mp hCompare

/-- The exact local-to-global criterion; this contains no analytic hypothesis. -/
theorem isColossallyAbundantFor_iff_primePower_maxima {ε : ℝ} {n : ℕ} :
    IsColossallyAbundantFor ε n ↔
      0 < ε ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ∀ k : ℕ,
        sigmaWeight ε (p ^ k) ≤ sigmaWeight ε (p ^ n.factorization p) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, fun p hp k => primePower_le_of_isColossallyAbundantFor h hp k⟩
  · rintro ⟨hε, hn, hLocal⟩
    exact isColossallyAbundantFor_of_primePower_maxima hε hn hLocal

end LeanEval.NumberTheory.Lagarias.Robin
