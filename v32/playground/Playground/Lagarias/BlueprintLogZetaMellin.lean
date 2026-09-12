import Playground.Lagarias.BlueprintLogZeta
import Playground.Lagarias.BlueprintPrimePowerSum
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The Mellin representation of the prime-power logarithm

Blueprint: Lemma 3.2. This proves the convergent identity
`log zeta(1+v) = v * integral_1^infty B(x) x^(-v-1)` for positive v.
Integrability and the L-series growth hypothesis are proved from the elementary
bound `0 <= B(x) <= H_floor(x) <= 1 + log x`; neither Mertens's theorem nor
its constant is used to justify this representation.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset MeasureTheory Filter Asymptotics
open scoped Topology ArithmeticFunction.vonMangoldt

noncomputable def primeLogCoeff (n : ℕ) : ℝ := Λ n / ((n : ℝ) * Real.log (n : ℝ))

lemma primeLogCoeff_nonneg (n : ℕ) : 0 ≤ primeLogCoeff n := by
  unfold primeLogCoeff
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n))

lemma primeLogCoeff_le_inv (n : ℕ) : primeLogCoeff n ≤ (n : ℝ)⁻¹ := by
  rcases n with _ | n
  · simp [primeLogCoeff]
  by_cases h1 : n + 1 = 1
  · have hn : n = 0 := by omega
    subst n
    norm_num [primeLogCoeff]
  have hn1 : (1 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast (show 1 < n + 1 by omega)
  have hn0 : (0 : ℝ) < (n + 1 : ℕ) := zero_lt_one.trans hn1
  have hlog : 0 < Real.log (n + 1 : ℕ) := Real.log_pos hn1
  have hratio : Λ (n + 1) / Real.log (n + 1 : ℕ) ≤ 1 :=
    (div_le_one hlog).mpr ArithmeticFunction.vonMangoldt_le_log
  unfold primeLogCoeff
  rw [mul_comm ((n + 1 : ℕ) : ℝ), ← div_div, ← one_div]
  exact div_le_div_of_nonneg_right hratio hn0.le

lemma B_eq_sum_coeff (x : ℝ) : B x = ∑ n ∈ Icc 1 ⌊x⌋₊, primeLogCoeff n :=
  B_eq_sum_vonMangoldt x

lemma B_nonneg (x : ℝ) : 0 ≤ B x := by
  rw [B_eq_sum_coeff]
  exact sum_nonneg fun n _ => primeLogCoeff_nonneg n

lemma B_le_harmonic (x : ℝ) : B x ≤ (harmonic ⌊x⌋₊ : ℝ) := by
  rw [B_eq_sum_coeff, harmonic_eq_sum_Icc]
  push_cast
  exact sum_le_sum fun n _ => primeLogCoeff_le_inv n

lemma B_le_one_add_log {x : ℝ} (hx : 1 ≤ x) : B x ≤ 1 + Real.log x := by
  have hn : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hn) (Nat.floor_le (zero_le_one.trans hx))
  exact (B_le_harmonic x).trans ((harmonic_le_one_add_log ⌊x⌋₊).trans (add_le_add_left hlog 1))

@[fun_prop] lemma measurable_B : Measurable B := by
  have heq : B = (fun N : ℕ => ∑ n ∈ Icc 1 N, primeLogCoeff n) ∘ Nat.floor :=
    funext B_eq_sum_coeff
  rw [heq]
  exact measurable_from_top.comp (by fun_prop)

lemma B_le_rpow {x r : ℝ} (hx : 1 ≤ x) (hr : 0 < r) :
    B x ≤ (1 + 1 / r) * x ^ r := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hp : 1 ≤ x ^ r := Real.one_le_rpow hx hr.le
  have hexp := Real.add_one_le_exp (r * Real.log x)
  have heq : Real.exp (r * Real.log x) = x ^ r := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  rw [heq] at hexp
  have hlog : Real.log x ≤ x ^ r / r := (le_div_iff₀ hr).mpr (by nlinarith only [hexp])
  calc
    B x ≤ 1 + Real.log x := B_le_one_add_log hx
    _ ≤ x ^ r + x ^ r / r := add_le_add hp hlog
    _ = (1 + 1 / r) * x ^ r := by ring

lemma coeff_sum_isBigO_rpow {r : ℝ} (hr : 0 < r) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, primeLogCoeff k) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  apply Asymptotics.IsBigO.of_bound (1 + 1 / r)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hBx : (∑ k ∈ Icc 1 n, primeLogCoeff k) = B (n : ℝ) := by
    simp only [B_eq_sum_coeff, Nat.floor_natCast]
  rw [hBx, Real.norm_of_nonneg (B_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
  exact B_le_rpow (by exact_mod_cast hn) hr

lemma integrableOn_B_mellin {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun x : ℝ => B x * x ^ (-v - 1)) (Set.Ioi 1) := by
  let r : ℝ := v / 2
  have hr : 0 < r := half_pos hv
  have he : r + (-v - 1) < -1 := by dsimp [r]; linarith
  have hmajor := (integrableOn_Ioi_rpow_of_lt he zero_lt_one).const_mul (1 + 1 / r)
  apply hmajor.mono' (by fun_prop)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  change 1 < x at hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  change ‖B x * x ^ (-v - 1)‖ ≤ (1 + 1 / r) * x ^ (r + (-v - 1))
  rw [norm_mul, Real.norm_of_nonneg (B_nonneg x),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  calc
    B x * x ^ (-v - 1) ≤ ((1 + 1 / r) * x ^ r) * x ^ (-v - 1) :=
      mul_le_mul_of_nonneg_right (B_le_rpow hx.le hr) (Real.rpow_nonneg hx0.le _)
    _ = (1 + 1 / r) * x ^ (r + (-v - 1)) := by rw [mul_assoc, Real.rpow_add hx0]

lemma primeLogCoeff_term {v : ℝ} (hv : 0 < v) (n : ℕ) :
    LSeries.term (fun n => (primeLogCoeff n : ℂ)) (v : ℂ) n =
      ((logZetaTerm (1 + v) n : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logZetaTerm]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℂ) ^ (v : ℂ) = (((n : ℝ) ^ v : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hn0.le v).symm
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hn), hpow, ← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  unfold primeLogCoeff logZetaTerm
  rw [Real.rpow_add hn0, Real.rpow_one, div_div]
  congr 1
  ring

lemma LSeries_primeLogCoeff {v : ℝ} (hv : 0 < v) :
    LSeries (fun n => (primeLogCoeff n : ℂ)) (v : ℂ) =
      ((Real.log (riemannZeta ((1 + v : ℝ) : ℂ)).re : ℝ) : ℂ) := by
  change (∑' n : ℕ, LSeries.term (fun n => (primeLogCoeff n : ℂ)) (v : ℂ) n) = _
  calc
    _ = ∑' n : ℕ, ((logZetaTerm (1 + v) n : ℝ) : ℂ) := tsum_congr (primeLogCoeff_term hv)
    _ = ((∑' n : ℕ, logZetaTerm (1 + v) n : ℝ) : ℂ) := by rw [Complex.ofReal_tsum]
    _ = _ := congrArg Complex.ofReal (log_zeta_eq_tsum (by linarith : 1 < 1 + v)).symm

/-- The absolutely convergent identity used in the normalization argument. -/
theorem log_zeta_eq_mellin_B {v : ℝ} (hv : 0 < v) :
    Real.log (riemannZeta ((1 + v : ℝ) : ℂ)).re =
      v * ∫ x : ℝ in Set.Ioi 1, B x * x ^ (-v - 1) := by
  have hm := LSeries_eq_mul_integral_of_nonneg primeLogCoeff
    (r := v / 2) (half_pos hv).le (s := (v : ℂ))
    (by simpa using (show v / 2 < v by linarith))
    (coeff_sum_isBigO_rpow (half_pos hv)) primeLogCoeff_nonneg
  have hsum (x : ℝ) : (∑ k ∈ Icc 1 ⌊x⌋₊, (primeLogCoeff k : ℂ)) = (B x : ℂ) := by
    rw [B_eq_sum_coeff]
    push_cast
    rfl
  simp_rw [hsum] at hm
  have hint : (∫ x : ℝ in Set.Ioi 1, (B x : ℂ) * (x : ℂ) ^ (-((v : ℂ) + 1))) =
      ((∫ x : ℝ in Set.Ioi 1, B x * x ^ (-v - 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (B x : ℂ) * (x : ℂ) ^ (-((v : ℂ) + 1)) = ((B x * x ^ (-v - 1) : ℝ) : ℂ)
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (by linarith [show 1 < x from hx] : 0 ≤ x)]
    push_cast
    congr 2
    ring
  rw [hint, LSeries_primeLogCoeff hv] at hm
  exact_mod_cast hm

end LeanEval.NumberTheory.Lagarias.Blueprint
