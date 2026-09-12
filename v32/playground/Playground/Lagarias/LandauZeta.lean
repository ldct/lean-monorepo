import Playground.Lagarias.LandauMGF
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Chebyshev

/-!
# The Chebyshev error transform and the logarithmic derivative of zeta

This module identifies an actual convergent integral with the meromorphic
expression used in Landau oscillation arguments. The identity holds initially
in `re s > 1`; continuation and oscillation are separate subsequent obligations.

The proof reuses Mathlib's Abel-summation formula for L-series and its proved
von Mangoldt logarithmic-derivative identity. No prime number theorem or RH
assumption is used here.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

open MeasureTheory Filter Finset Asymptotics
open scoped Topology ArithmeticFunction.vonMangoldt

lemma psi_eq_sum_Icc_one (x : ℝ) :
    Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by
  unfold Chebyshev.psi
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  · intro n hn
    rfl

lemma sum_vonMangoldt_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, Λ k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (Real.log 4 + 4)
  apply Filter.Eventually.of_forall
  intro n
  have heq : (∑ k ∈ Finset.Icc 1 n, Λ k) = Chebyshev.psi (n : ℝ) := by
    simp only [psi_eq_sum_Icc_one, Nat.floor_natCast]
  rw [heq, Real.norm_of_nonneg (Chebyshev.psi_nonneg _), Real.rpow_one,
    Real.norm_of_nonneg (Nat.cast_nonneg n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

/-- The Mellin integral of the Chebyshev summatory function. -/
noncomputable def psiMellin (s : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 1, (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- The corresponding transform of the prime-counting error `psi(x) - x`. -/
noncomputable def psiErrorMellin (s : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 1, ((Chebyshev.psi x - x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))

lemma vonMangoldt_LSeries_eq_mul_psiMellin {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) s = s * psiMellin s := by
  have h := LSeries_eq_mul_integral_of_nonneg ArithmeticFunction.vonMangoldt
    (r := 1) (by norm_num) hs sum_vonMangoldt_isBigO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg)
  have hsum (x : ℝ) : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ)) = (Chebyshev.psi x : ℂ) := by
    rw [psi_eq_sum_Icc_one]
    push_cast
    rfl
  simpa only [psiMellin, hsum] using h

/-- The Chebyshev transform is the logarithmic derivative of zeta divided by `-s`. -/
theorem psiMellin_eq_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    psiMellin s = -deriv riemannZeta s / (s * riemannZeta s) := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hmul : s * psiMellin s = -deriv riemannZeta s / riemannZeta s :=
    (vonMangoldt_LSeries_eq_mul_psiMellin hs).symm.trans
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)
  calc
    psiMellin s = (s * psiMellin s) / s := by field_simp
    _ = (-deriv riemannZeta s / riemannZeta s) / s := by rw [hmul]
    _ = -deriv riemannZeta s / (s * riemannZeta s) := by rw [div_div, mul_comm]

/-- Linear growth suffices for convergence of the summatory-function kernel. -/
lemma integrableOn_mul_cpow_of_linear_bound {f : ℝ → ℂ} (hfm : Measurable f)
    {C : ℝ} (hbound : ∀ x : ℝ, 1 < x → ‖f x‖ ≤ C * x)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => f x * (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hExp : -(s + 1) ≠ 0 := by
    intro h
    have h' : -(s.re + 1) = 0 := by simpa using congrArg Complex.re h
    linarith
  have hk : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    intro x hx
    exact (differentiableAt_id.ofReal_cpow_const
      (ne_of_gt (zero_lt_one.trans hx)) hExp).continuousAt.continuousWithinAt
  have hmajor := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) zero_lt_one).const_mul C
  apply hmajor.mono' (hfm.aestronglyMeasurable.mul (hk.aestronglyMeasurable measurableSet_Ioi))
  apply (ae_restrict_iff' measurableSet_Ioi).2
  exact ae_of_all _ fun x hx => by
    dsimp only
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    calc
      ‖f x‖ * x ^ (-(s.re + 1)) ≤ (C * x) * x ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right (hbound x hx) (Real.rpow_nonneg hx0.le _)
      _ = C * (x ^ (1 : ℝ) * x ^ (-(s.re + 1))) := by rw [Real.rpow_one]; ring
      _ = C * x ^ ((1 : ℝ) + (-(s.re + 1))) := by rw [Real.rpow_add hx0]
      _ = C * x ^ (-s.re) := by congr 2; ring

lemma integrableOn_psiMellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) := by
  apply integrableOn_mul_cpow_of_linear_bound
    (Complex.continuous_ofReal.measurable.comp Chebyshev.psi_mono.measurable)
    (C := Real.log 4 + 4) ?_ hs
  intro x hx
  rw [Complex.norm_real, Real.norm_of_nonneg (Chebyshev.psi_nonneg x)]
  exact Chebyshev.psi_le_const_mul_self (by linarith)

lemma mul_cpow_kernel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
  calc
    (x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
        (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
    _ = (x : ℂ) ^ ((1 : ℂ) + (-(s + 1))) :=
      (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')).symm
    _ = (x : ℂ) ^ (-s) := by congr 1; ring

lemma integral_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    (∫ x : ℝ in Set.Ioi 1, (x : ℂ) ^ (-s)) = 1 / (s - 1) := by
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) zero_lt_one,
    Complex.ofReal_one, Complex.one_cpow, show -s + 1 = -(s - 1) by ring,
    neg_div_neg_eq]

lemma integrableOn_psiErrorMellin {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => ((Chebyshev.psi x - x : ℝ) : ℂ) *
      (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hmain := integrableOn_Ioi_cpow_of_lt (a := -s)
    (by simpa using neg_lt_neg hs) zero_lt_one
  apply ((integrableOn_psiMellin hs).sub hmain).congr
  apply (ae_restrict_iff' measurableSet_Ioi).2
  exact ae_of_all _ fun x hx => by
    dsimp only
    rw [← mul_cpow_kernel (zero_lt_one.trans hx) s]
    push_cast
    ring

/-- The exact convergent integral expression whose continued poles encode zeta zeros. -/
theorem psiErrorMellin_eq_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    psiErrorMellin s = -deriv riemannZeta s / (s * riemannZeta s) - 1 / (s - 1) := by
  have hmain := integrableOn_Ioi_cpow_of_lt (a := -s)
    (by simpa using neg_lt_neg hs) zero_lt_one
  calc
    psiErrorMellin s = psiMellin s - ∫ x : ℝ in Set.Ioi 1, (x : ℂ) ^ (-s) := by
      rw [psiErrorMellin, psiMellin, ← integral_sub (integrableOn_psiMellin hs) hmain]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      rw [← mul_cpow_kernel (zero_lt_one.trans hx) s]
      push_cast
      ring
    _ = -deriv riemannZeta s / (s * riemannZeta s) - 1 / (s - 1) := by
      rw [psiMellin_eq_logDeriv_zeta hs, integral_cpow_neg hs]

end LeanEval.NumberTheory.Lagarias.Landau
