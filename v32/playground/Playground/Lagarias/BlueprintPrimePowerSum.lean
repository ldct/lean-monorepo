import Playground.Lagarias.BlueprintLCM
import Mathlib.Data.Nat.Prime.Int

/-!
# The two finite representations of the prime-power logarithm

Blueprint: equation (3.3). A finite bijection sends `(p,k)` to `p^k` and proves
that grouping by prime agrees with summing the von Mangoldt coefficients.
This connects the LCM argument's `B` to Abel summation without assuming a
prime-power identity as an analytic hypothesis.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset
open scoped ArithmeticFunction.vonMangoldt

lemma sum_prime_powers_by_base {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    (∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (Nat.log p n), f (p ^ k)) =
      ∑ m ∈ (Icc 1 n).filter IsPrimePow, f m := by
  classical
  rw [sum_sigma']
  apply sum_bij (fun pk _ => pk.1 ^ pk.2)
  · rintro ⟨p, k⟩ hpk
    obtain ⟨hp, hk⟩ := mem_sigma.mp hpk
    obtain ⟨hk1, hklog⟩ := mem_Icc.mp hk
    have hprime := Nat.prime_of_mem_primesLE hp
    apply mem_filter.mpr
    constructor
    · exact mem_Icc.mpr ⟨Nat.one_le_pow k p hprime.pos,
        Nat.pow_le_of_le_log (by omega) hklog⟩
    · exact isPrimePow_nat_iff.mpr ⟨p, k, hprime, by omega, rfl⟩
  · rintro ⟨p, k⟩ hp ⟨q, j⟩ hq heq
    obtain ⟨hpp, hkk⟩ := mem_sigma.mp hp
    obtain ⟨hqq, hjj⟩ := mem_sigma.mp hq
    have hkp : k ≠ 0 := by have := (mem_Icc.mp hkk).1; omega
    have hjp : j ≠ 0 := by have := (mem_Icc.mp hjj).1; omega
    obtain ⟨rfl, rfl⟩ := (Nat.prime_of_mem_primesLE hpp).pow_inj'
      (Nat.prime_of_mem_primesLE hqq) hkp hjp heq
    rfl
  · intro m hm
    obtain ⟨hmrange, hmpow⟩ := mem_filter.mp hm
    obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff.mp hmpow
    obtain ⟨hmpos, hmle⟩ := mem_Icc.mp hmrange
    have hpn : p ≤ n := (Nat.le_of_dvd (by omega) (dvd_pow_self p hk.ne')).trans hmle
    refine ⟨⟨p, k⟩, mem_sigma.mpr ⟨?_, mem_Icc.mpr ⟨by omega, ?_⟩⟩, rfl⟩
    · exact Nat.mem_primesLE.mpr ⟨hp, hpn⟩
    · exact Nat.le_log_of_pow_le hp.one_lt hmle
  · intro pk hpk
    rfl

/-- Weighted prime-power regrouping, including all endpoint powers. -/
lemma sum_vonMangoldt_mul_eq_sum_prime_powers (f : ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ Icc 1 n, Λ m * f m) =
      ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (Nat.log p n), Real.log (p : ℝ) * f (p ^ k) := by
  classical
  have hfilter : (∑ m ∈ Icc 1 n, Λ m * f m) =
      ∑ m ∈ (Icc 1 n).filter IsPrimePow, Λ m * f m := by
    rw [sum_filter]
    apply sum_congr rfl
    intro m hm
    by_cases hp : IsPrimePow m
    · simp [hp]
    · simp [hp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp]
  rw [hfilter, ← sum_prime_powers_by_base (fun m => Λ m * f m) n]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
    ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]

lemma primeLogPartial_eq_sum_Icc (p : ℝ) (a : ℕ) :
    primeLogPartial p a = ∑ k ∈ Icc 1 a, p⁻¹ ^ k / (k : ℝ) := by
  unfold primeLogPartial logPartial logTerm
  simp_rw [← Nat.cast_one, ← Nat.cast_add]
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k : ℕ => p⁻¹ ^ k / (k : ℝ)) 0 a (c := 1)]
  simp only [Nat.zero_add, Finset.Ico_add_one_right_eq_Icc]

/-- Equation (3.3), now identifying the exact `B` used in the proved LCM estimate. -/
theorem B_eq_sum_vonMangoldt (x : ℝ) :
    B x = ∑ m ∈ Icc 1 ⌊x⌋₊, Λ m / ((m : ℝ) * Real.log (m : ℝ)) := by
  have hweighted := sum_vonMangoldt_mul_eq_sum_prime_powers
    (fun m => (((m : ℝ) * Real.log (m : ℝ))⁻¹)) ⌊x⌋₊
  simp only [← div_eq_mul_inv] at hweighted
  rw [hweighted]
  unfold B K
  apply sum_congr rfl
  intro p hp
  rw [primeLogPartial_eq_sum_Icc]
  apply sum_congr rfl
  intro k hk
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hpR).ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := (mem_Icc.mp hk).1; omega)
  push_cast
  rw [Real.log_pow, inv_pow]
  field_simp

lemma B_eq_sum_Ioc_vonMangoldt (x : ℝ) :
    B x = ∑ m ∈ Ioc 0 ⌊x⌋₊, Λ m / ((m : ℝ) * Real.log (m : ℝ)) := by
  rw [B_eq_sum_vonMangoldt]
  congr 1
  ext m
  simp only [mem_Icc, mem_Ioc]
  omega

end LeanEval.NumberTheory.Lagarias.Blueprint
