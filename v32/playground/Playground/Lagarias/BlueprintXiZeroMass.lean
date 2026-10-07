import Playground.Lagarias.BlueprintXiZeros
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# The total mass of the actual zeta zeros

Blueprint: Lemma 4.1. The same polynomial in the genuine Hadamard
factorization is used at zero and one; its derivative is constant and cancels.
The values of the completed zeta function then identify the sum. Under the
actual Riemann hypothesis it becomes the positive inverse-square zero mass.
No numerical zero ordinates or an assumed zero-sum identity are used.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Complex
open scoped ComplexConjugate

noncomputable def xiZeroTerm (i : XiZero) : ℂ := 1 / (xiZero i * (1 - xiZero i))
noncomputable def xiZeroMass : ℝ := ∑' i : XiZero, ‖xiZero i‖⁻¹ ^ (2 : ℕ)

lemma xiZeroTerm_eq (i : XiZero) :
    xiZeroTerm i = 1 / (1 - xiZero i) + 1 / xiZero i := by
  have hz := xiZero_ne_zero i
  have hz1 : 1 - xiZero i ≠ 0 := sub_ne_zero.mpr (one_ne_xiZero i)
  unfold xiZeroTerm
  field_simp
  ring

lemma summable_xiZeroTerm : Summable xiZeroTerm := by
  have hs := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ one_ne_xiZero
  exact hs.congr (fun i => (xiZeroTerm_eq i).symm)

set_option backward.isDefEq.respectTransparency false in
lemma hasDerivAt_xi (s : ℂ) :
    HasDerivAt Complex.riemannXi
      (((2 * s - 1) * completedRiemannZeta₀ s +
        s * (s - 1) * deriv completedRiemannZeta₀ s) / 2) s := by
  have hd := ((((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).mul
    (differentiable_completedZeta₀ s).hasDerivAt).add_const 1).div_const 2
  convert! hd using 1 <;> simp only [Complex.riemannXi, id_eq] <;> ring

lemma logDeriv_xi_zero : logDeriv Complex.riemannXi 0 = -completedRiemannZeta₀ 0 := by
  change deriv Complex.riemannXi 0 / Complex.riemannXi 0 = _
  rw [(hasDerivAt_xi 0).deriv, Complex.riemannXi_zero]
  ring

lemma logDeriv_xi_one : logDeriv Complex.riemannXi 1 = completedRiemannZeta₀ 1 := by
  change deriv Complex.riemannXi 1 / Complex.riemannXi 1 = _
  rw [(hasDerivAt_xi 1).deriv, xi_one]
  ring

lemma polynomial_derivative_constant {P : Polynomial ℂ} (hP : P.degree ≤ 1) :
    P.derivative = Polynomial.C (P.coeff 1) := by
  have hnat : P.natDegree ≤ 1 := Polynomial.natDegree_le_of_degree_le hP
  have hform := Polynomial.eq_X_add_C_of_natDegree_le_one hnat
  nth_rw 1 [hform]
  simp

/-- Subtracting the two evaluations cancels the same Hadamard linear term. -/
theorem tsum_xiZeroTerm_eq_logDeriv_sub :
    (∑' i : XiZero, xiZeroTerm i) =
      logDeriv Complex.riemannXi 1 - logDeriv Complex.riemannXi 0 := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have h0 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac zero_ne_xiZero
  have h1 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac one_ne_xiZero
  have hder := polynomial_derivative_constant hdeg
  rw [hder] at h0 h1
  simp only [Polynomial.eval_C, zero_sub, one_div, inv_neg, neg_add_cancel,
    tsum_zero, add_zero] at h0
  simp only [Polynomial.eval_C] at h1
  calc
    _ = ∑' i : XiZero, (1 / (1 - xiZero i) + 1 / xiZero i) := tsum_congr xiZeroTerm_eq
    _ = _ := by rw [h1, h0]; ring

/-- Equation (4.13), including all zero multiplicities. -/
theorem tsum_xiZeroTerm_eq :
    (∑' i : XiZero, xiZeroTerm i) =
      2 + (Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ)) := by
  rw [tsum_xiZeroTerm_eq_logDeriv_sub, logDeriv_xi_one, logDeriv_xi_zero,
    completedRiemannZeta₀_one, completedRiemannZeta₀_zero]
  ring

lemma one_sub_xiZero_eq_conj (hRH : RiemannHypothesis) (i : XiZero) :
    1 - xiZero i = conj (xiZero i) := by
  apply Complex.ext <;> simp [xiZero_re_eq_half hRH i] <;> ring

lemma xiZeroTerm_eq_inv_sq (hRH : RiemannHypothesis) (i : XiZero) :
    xiZeroTerm i = ((‖xiZero i‖⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold xiZeroTerm
  rw [one_sub_xiZero_eq_conj hRH i, Complex.mul_conj']
  push_cast
  simp only [one_div, inv_pow]

/-- Under RH the unconditional complex identity is the positive zero-mass identity. -/
theorem xiZeroMass_eq (hRH : RiemannHypothesis) :
    xiZeroMass = 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    have hh := Complex.ofReal_log (show 0 ≤ 4 * Real.pi by positivity)
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hh.symm
  have heq : (xiZeroMass : ℂ) =
      ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [xiZeroMass, Complex.ofReal_tsum]
    calc
      _ = ∑' i : XiZero, xiZeroTerm i := tsum_congr (fun i => (xiZeroTerm_eq_inv_sq hRH i).symm)
      _ = _ := by rw [tsum_xiZeroTerm_eq, hlog]; push_cast; rfl
  exact_mod_cast heq

lemma xiZeroMass_nonneg : 0 ≤ xiZeroMass := tsum_nonneg (fun i => sq_nonneg _)

/-- This coefficient comparison is already unconditional, since the zeros
lie in the closed right half-plane. -/
lemma norm_xiZero_le_norm_add_one (i : XiZero) : ‖xiZero i‖ ≤ ‖xiZero i + 1‖ := by
  have h0 := (xi_zero_re_mem_strip (xiZero_is_zero i)).1
  have hs : ‖xiZero i‖ ^ 2 ≤ ‖xiZero i + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
    nlinarith
  nlinarith [norm_nonneg (xiZero i), norm_nonneg (xiZero i + 1)]

lemma norm_xi_integrated_coefficient_le (i : XiZero) :
    ‖1 / (xiZero i * (xiZero i + 1))‖ ≤ ‖xiZero i‖⁻¹ ^ (2 : ℕ) := by
  have hn : 0 < ‖xiZero i‖ := norm_pos_iff.mpr (xiZero_ne_zero i)
  rw [norm_div, norm_one, norm_mul, ← one_div_pow]
  apply div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hn)
  simpa only [pow_two] using
    mul_le_mul_of_nonneg_left (norm_xiZero_le_norm_add_one i) hn.le

/-- Absolute summability of the coefficients in the integrated explicit formula. -/
lemma summable_xi_integrated_coefficient :
    Summable (fun i : XiZero => 1 / (xiZero i * (xiZero i + 1))) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) norm_xi_integrated_coefficient_le
    summable_xiZero_inv_sq

end LeanEval.NumberTheory.Lagarias.Blueprint
