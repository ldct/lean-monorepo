import Playground.Lagarias.BlueprintLocalFactor
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The logarithm of zeta and the prime-power coefficients

Blueprint: the Euler-product identity used to identify the constant in
Lemma 3.2. We expand the already proved Euler product and regroup absolutely
summable prime-power terms. The real logarithm is recovered by applying `re`
to the complex exponential identity; no choice of a logarithm branch is
assumed and no zeta-zero theorem is needed.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable def logZetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  Λ n / ((n : ℝ) ^ s * Real.log (n : ℝ))

lemma logZetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ logZetaTerm s n := by
  unfold logZetaTerm
  apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.log_natCast_nonneg n)

lemma logZetaTerm_le (s : ℝ) (n : ℕ) : logZetaTerm s n ≤ 1 / (n : ℝ) ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logZetaTerm]
  by_cases h1 : n = 1
  · simp [h1, logZetaTerm]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hratio : Λ n / Real.log (n : ℝ) ≤ 1 :=
    (div_le_one hlog).mpr ArithmeticFunction.vonMangoldt_le_log
  unfold logZetaTerm
  calc
    Λ n / ((n : ℝ) ^ s * Real.log (n : ℝ)) =
        (Λ n / Real.log (n : ℝ)) / (n : ℝ) ^ s := by rw [div_div, mul_comm]
    _ ≤ 1 / (n : ℝ) ^ s :=
      div_le_div_of_nonneg_right hratio (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma summable_logZetaTerm {s : ℝ} (hs : 1 < s) : Summable (logZetaTerm s) :=
  (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
    (logZetaTerm_nonneg s) (logZetaTerm_le s)

lemma logZetaTerm_prime_pow (s : ℝ) (p : Nat.Primes) (k : ℕ) :
    logZetaTerm s ((p : ℕ) ^ (k + 1)) =
      ((p : ℝ) ^ (-s)) ^ (k + 1) / ((k : ℝ) + 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hl0 : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  unfold logZetaTerm
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  push_cast
  rw [Real.log_pow]
  have heq : ((p : ℝ) ^ (-s)) ^ (k + 1) = ((p : ℝ) ^ (k + 1)) ^ (-s) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (k + 1),
      ← Real.rpow_natCast (p : ℝ) (k + 1), ← Real.rpow_mul hp0.le,
      ← Real.rpow_mul hp0.le]
    congr 1
    ring
  rw [heq, Real.rpow_neg (pow_nonneg hp0.le _)]
  field_simp

lemma logZetaTerm_tsum_eq_prime_sum {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, logZetaTerm s n) =
      ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) := by
  have hsummable := summable_logZetaTerm hs
  have hsupport : Function.support (logZetaTerm s) ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hnot
    exact hn (by simp [logZetaTerm, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot])
  calc
    (∑' n : ℕ, logZetaTerm s n) =
        ∑' n : {n : ℕ // IsPrimePow n}, logZetaTerm s n :=
      (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' (p : Nat.Primes) (k : ℕ), logZetaTerm s (p ^ (k + 1)) :=
      (tsum_primes_pow_eq hsummable.subtype).symm
    _ = ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) := by
      apply tsum_congr
      intro p
      simp_rw [logZetaTerm_prime_pow]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
      have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      have hq0 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg hp0.le _
      have hq1 : (p : ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      exact (hasSum_logTerm hq0 hq1).tsum_eq

/-- The real logarithmic zeta series used in the normalization argument. -/
theorem log_zeta_eq_tsum {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re = ∑' n : ℕ, logZetaTerm s n := by
  let T : ℝ := ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s))
  have hterm (p : Nat.Primes) :
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) =
        ((-Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    have hq1 : (p : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hpow : (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp0.le]
      push_cast
      rfl
    rw [hpow, show (1 : ℂ) - (((p : ℝ) ^ (-s) : ℝ) : ℂ) =
      ((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (sub_nonneg.mpr hq1.le), Complex.ofReal_neg]
  have hsum : (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))) = (T : ℂ) := by
    rw [T, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hEuler := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) (by simpa using hs)
  rw [hsum, Complex.exp_ofReal] at hEuler
  have hre : Real.exp T = (riemannZeta (s : ℂ)).re := by
    simpa using congrArg Complex.re hEuler
  rw [← hre, Real.log_exp]
  exact (logZetaTerm_tsum_eq_prime_sum hs).symm

end LeanEval.NumberTheory.Lagarias.Blueprint
