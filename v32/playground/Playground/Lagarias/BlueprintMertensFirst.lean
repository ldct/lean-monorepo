import Playground.Lagarias.BlueprintSmoothing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The first elementary Mertens estimate

Blueprint: the first paragraph of the proof of Lemma 3.2. This file proves
`A(x) = log x + O(1)` with an explicit bound, without a prime number theorem.
The argument uses the divisor identity for von Mangoldt, a factorial-logarithm
integral comparison, and the existing elementary Chebyshev bound.

The sum/integral organization can also be found in Mathlib's
`Analysis.SumIntegralComparisons` and the PrimeNumberTheoremAnd project's
`IEANTN/Mertens.lean`. No theorem from that external project is an assumption
or an imported dependency here.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable def A (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n : ℝ)
noncomputable def firstError (x : ℝ) : ℝ := A x - Real.log x
noncomputable def logFactorialSum (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (n : ℝ)

lemma logFactorialSum_eq_mangoldt (x : ℝ) :
    logFactorialSum x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / (d : ℝ)⌋₊ : ℝ) := by
  unfold logFactorialSum
  have h (n : ℕ) : Real.log (n : ℝ) =
      (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) n := by
    simp [ArithmeticFunction.vonMangoldt_mul_zeta]
  simp_rw [h, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

lemma mul_A_eq_sum (x : ℝ) :
    x * A x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / (d : ℝ)) := by
  unfold A
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro d hd
  ring

lemma logFactorialSum_le {x : ℝ} (hx : 1 ≤ x) : logFactorialSum x ≤ x * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  unfold logFactorialSum
  calc
    (∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log (n : ℝ)) ≤ ∑ _n ∈ Ioc 0 ⌊x⌋₊, Real.log x := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn0, hnx⟩ := mem_Ioc.mp hn
      apply Real.log_le_log (by exact_mod_cast hn0)
      exact (by exact_mod_cast hnx : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx0)
    _ = (⌊x⌋₊ : ℝ) * Real.log x := by simp
    _ ≤ x * Real.log x := mul_le_mul_of_nonneg_right (Nat.floor_le hx0) (Real.log_nonneg hx)

lemma logFactorialSum_nat_ge {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ logFactorialSum (n : ℝ) := by
  have hmono : MonotoneOn Real.log (Set.Icc (1 : ℝ) (n : ℝ)) := by
    intro x hx y hy hxy
    exact Real.log_le_log (by linarith [hx.1]) hxy
  have hint := MonotoneOn.integral_le_sum_Ico hn hmono
  have hsum : logFactorialSum (n : ℝ) = ∑ k ∈ Ico 1 n, Real.log ((k + 1 : ℕ) : ℝ) := by
    unfold logFactorialSum
    rw [Nat.floor_natCast]
    change (∑ k ∈ Icc 1 n, Real.log (k : ℝ)) = _
    rw [← add_sum_Ioc_eq_sum_Icc hn]
    simp only [Nat.cast_one, Real.log_one, zero_add]
    change (∑ k ∈ Ico (1 + 1) (n + 1), Real.log (k : ℝ)) = _
    rw [← Finset.sum_Ico_add']
  rw [← hsum] at hint
  rw [integral_log] at hint
  norm_num at hint
  linarith

lemma logFactorialSum_le_mul_A {x : ℝ} (hx : 0 ≤ x) : logFactorialSum x ≤ x * A x := by
  rw [logFactorialSum_eq_mangoldt, mul_A_eq_sum]
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left
    (Nat.floor_le (div_nonneg hx (Nat.cast_nonneg d))) ArithmeticFunction.vonMangoldt_nonneg

lemma mul_A_le_logFactorialSum_add_psi {x : ℝ} :
    x * A x ≤ logFactorialSum x + Chebyshev.psi x := by
  rw [mul_A_eq_sum, logFactorialSum_eq_mangoldt, Chebyshev.psi, ← Finset.sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hfloor := (Nat.lt_floor_add_one (x / (d : ℝ))).le
  have hmul := mul_le_mul_of_nonneg_left hfloor (ArithmeticFunction.vonMangoldt_nonneg (n := d))
  nlinarith only [hmul]

lemma A_nat_ge {n : ℕ} (hn : 1 ≤ n) : Real.log (n : ℝ) - 1 ≤ A (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle := (logFactorialSum_nat_ge hn).trans
    (logFactorialSum_le_mul_A hn0.le)
  apply (mul_le_mul_left hn0).mp
  nlinarith only [hle]

lemma firstError_ge {x : ℝ} (hx : 2 ≤ x) : -2 ≤ firstError x := by
  let n : ℕ := ⌊x⌋₊
  have hn1 : 1 ≤ n := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by norm_num; linarith)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hAx : A (n : ℝ) = A x := by simp only [A, n, Nat.floor_natCast]
  have hbase := A_nat_ge hn1
  rw [hAx] at hbase
  have hlog := log_le_tangent hn0 (by linarith : 0 < x)
  have hfloor : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have herr : (x - (n : ℝ)) / (n : ℝ) ≤ 1 := (div_le_iff₀ hn0).mpr (by linarith)
  unfold firstError
  linarith

lemma firstError_le {x : ℝ} (hx : 1 ≤ x) : firstError x ≤ Real.log 4 + 4 := by
  have hx0 : 0 < x := by linarith
  have hle := (mul_A_le_logFactorialSum_add_psi (x := x)).trans
    (add_le_add (logFactorialSum_le hx) (Chebyshev.psi_le_const_mul_self hx0.le))
  have hA : A x ≤ Real.log x + Real.log 4 + 4 := by
    apply (mul_le_mul_left hx0).mp
    nlinarith only [hle]
  unfold firstError
  linarith

/-- The bounded error required by the elementary prime-power Mertens proof. -/
theorem abs_firstError_le_seven {x : ℝ} (hx : 2 ≤ x) : |firstError x| ≤ 7 := by
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hlo := firstError_ge hx
  have hhi := firstError_le (by linarith : 1 ≤ x)
  rw [abs_le]
  constructor <;> linarith

lemma measurable_A : Measurable A := by
  have h : Measurable (fun N : ℕ => ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ)) := measurable_from_top
  exact h.comp (by fun_prop)

lemma measurable_firstError : Measurable firstError :=
  measurable_A.sub Real.measurable_log

end LeanEval.NumberTheory.Lagarias.Blueprint
