import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# The actual xi zeros, including multiplicities

Blueprint: Section 4.3. We use the zero-divisor index from the verified
Hadamard factorization, not an arbitrary sequence of putative zeros.
Every indexed point is proved to be a zero of the actual entire xi function,
the closed-strip location is derived from the functional equation and Euler
product, and Mathlib's unchanged `RiemannHypothesis` then places these points
on the critical line. The inverse-square summability is unconditional.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Complex Set

noncomputable abbrev XiZero := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)

noncomputable abbrev xiZero (i : XiZero) : ℂ := Complex.Hadamard.divisorZeroIndex₀_val i

lemma xi_one : Complex.riemannXi 1 = 1 / 2 := by
  calc
    Complex.riemannXi 1 = Complex.riemannXi 0 := by
      simpa only [sub_zero] using Complex.riemannXi_one_sub (0 : ℂ)
    _ = 1 / 2 := Complex.riemannXi_zero

lemma xiZero_ne_zero (i : XiZero) : xiZero i ≠ 0 :=
  Complex.Hadamard.divisorZeroIndex₀_val_ne_zero i

lemma xiZero_is_zero (i : XiZero) : Complex.riemannXi (xiZero i) = 0 := by
  by_contra hne
  have ha : AnalyticOnNhd ℂ Complex.riemannXi (Set.univ : Set ℂ) :=
    fun z _ => Complex.differentiable_riemannXi.analyticAt z
  have hdiv : MeromorphicOn.divisor Complex.riemannXi (Set.univ : Set ℂ) (xiZero i) = 0 := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ _),
      (Complex.differentiable_riemannXi.analyticAt (xiZero i)).analyticOrderAt_eq_zero.mpr hne]
    simp
  exact Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support i hdiv

lemma xiZero_ne_one (i : XiZero) : xiZero i ≠ 1 := by
  intro heq
  have hz := xiZero_is_zero i
  rw [heq, xi_one] at hz
  norm_num at hz

lemma completedZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro heq
    rw [heq, Complex.zero_re] at hs
    linarith
  intro hz
  apply riemannZeta_ne_zero_of_one_lt_re hs
  rw [riemannZeta_def_of_ne_zero hs0, hz, zero_div]

lemma xi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Complex.riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro heq
    rw [heq, Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro heq
    rw [heq, Complex.one_re] at hs
    exact (lt_irrefl (1 : ℝ)) hs
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
      (completedZeta_ne_zero_of_one_lt_re hs)) (by norm_num)

/-- The functional equation and Euler product suffice for the closed strip. -/
lemma xi_zero_re_mem_strip {s : ℂ} (hs : Complex.riemannXi s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  have hright : s.re ≤ 1 := by
    by_contra h
    exact xi_ne_zero_of_one_lt_re (lt_of_not_ge h) hs
  constructor
  · by_contra h
    have hleft : 1 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    apply xi_ne_zero_of_one_lt_re hleft
    rw [Complex.riemannXi_one_sub, hs]
  · exact hright

lemma zeta_zero_of_xi_zero {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hs : Complex.riemannXi s = 0) : riemannZeta s = 0 := by
  have hcoef : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta hs0 hs1] at hs
  have hmul : (s * (s - 1)) * completedRiemannZeta s = 0 :=
    (div_eq_zero_iff.mp hs).resolve_right (by norm_num)
  have hc : completedRiemannZeta s = 0 := (mul_eq_zero.mp hmul).resolve_left hcoef
  rw [riemannZeta_def_of_ne_zero hs0, hc, zero_div]

lemma xiZero_is_zeta_zero (i : XiZero) : riemannZeta (xiZero i) = 0 :=
  zeta_zero_of_xi_zero (xiZero_ne_zero i) (xiZero_ne_one i) (xiZero_is_zero i)

lemma xiZero_not_trivial (i : XiZero) :
    ¬∃ n : ℕ, xiZero i = -2 * (n + 1) := by
  rintro ⟨n, hn⟩
  have hnonneg := (xi_zero_re_mem_strip (xiZero_is_zero i)).1
  have hre : (xiZero i).re = -2 * ((n : ℝ) + 1) := by
    simpa using congrArg Complex.re hn
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- This hypothesis is exactly Mathlib's Riemann hypothesis, with its original
exclusion of trivial zeros, rather than a bespoke assumption about the index. -/
theorem xiZero_re_eq_half (hRH : RiemannHypothesis) (i : XiZero) :
    (xiZero i).re = 1 / 2 :=
  hRH (xiZero i) (xiZero_is_zeta_zero i) (xiZero_not_trivial i) (xiZero_ne_one i)

/-- The unconditional zero summability furnished by the verified factorization. -/
theorem summable_xiZero_inv_sq :
    Summable (fun i : XiZero => ‖xiZero i‖⁻¹ ^ (2 : ℕ)) :=
  summable_riemannXi_divisorZeroIndex₀_norm_inv_sq

lemma one_ne_xiZero (i : XiZero) : (1 : ℂ) ≠ xiZero i := (xiZero_ne_one i).symm

lemma zero_ne_xiZero (i : XiZero) : (0 : ℂ) ≠ xiZero i := (xiZero_ne_zero i).symm

end LeanEval.NumberTheory.Lagarias.Blueprint
