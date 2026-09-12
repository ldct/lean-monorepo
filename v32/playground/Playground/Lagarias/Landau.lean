import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Positivity and analytic continuation of Dirichlet series

This module develops the positivity argument used in Landau's theorem on the
singularity at a finite abscissa of convergence. It is independent of Robin's
theorems and of the still-incomplete target in `v32/Lagarias.lean`.

The Tonelli step converts summability of nonnegative logarithmic moments and
of their exponential generating series into convergence further to the left.
The Taylor series of a holomorphic continuation supplies that generating series.
-/

namespace LeanEval.NumberTheory.Lagarias.Landau

/-- The nonnegative double-series step in Landau's continuation argument. -/
theorem summable_weighted_exp_of_moments {w x : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hx : ∀ n, 0 ≤ x n)
    (hm : ∀ k : ℕ, Summable (fun n : ℕ => w n * x n ^ k))
    (hs : Summable (fun k : ℕ => (∑' n : ℕ, w n * x n ^ k) / (k.factorial : ℝ))) :
    Summable (fun n : ℕ => w n * Real.exp (x n)) := by
  let F : ℕ × ℕ → ℝ := fun p => w p.2 * x p.2 ^ p.1 / (p.1.factorial : ℝ)
  have hF0 : ∀ p, 0 ≤ F p := by
    intro p
    exact div_nonneg (mul_nonneg (hw _) (pow_nonneg (hx _) _)) (Nat.cast_nonneg _)
  have hF : Summable F := by
    apply (summable_prod_of_nonneg hF0).2
    constructor
    · intro k
      exact (hm k).div_const (k.factorial : ℝ)
    · simpa only [F, tsum_div_const] using hs
  have hswap : Summable (fun p : ℕ × ℕ => F (p.2, p.1)) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr hF
  have hrows : Summable (fun n : ℕ => ∑' k : ℕ, F (k, n)) :=
    ((summable_prod_of_nonneg (fun p => hF0 (p.2, p.1))).1 hswap).2
  have heq (n : ℕ) : (∑' k : ℕ, F (k, n)) = w n * Real.exp (x n) := by
    calc
      (∑' k : ℕ, F (k, n)) = w n * ∑' k : ℕ, x n ^ k / (k.factorial : ℝ) := by
        simp only [F, mul_div_assoc, tsum_mul_left]
      _ = w n * Real.exp (x n) := by rw [(Real.hasSum_exp (x n)).tsum_eq]
  simpa only [heq] using hrows

/-- Natural-number logarithms, including `log 0 = 0`, are nonnegative. -/
lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n

/-- Expand Mathlib's iterated logarithmic multiplication operator. -/
lemma logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = Complex.log (n : ℂ) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
      ring

/-- The norm of a logarithmically weighted Dirichlet term is its nonnegative moment. -/
lemma norm_term_logMul_iterate (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    ‖LSeries.term (LSeries.logMul^[k] f) s n‖ =
      ‖LSeries.term f s n‖ * Real.log (n : ℝ) ^ k := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn,
      logMul_iterate_apply, norm_mul, norm_pow, ← Complex.natCast_log,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (log_nat_nonneg n)]
    ring

/-- Every logarithmic moment is summable strictly inside the convergence half-plane. -/
lemma summable_log_moments {f : ℕ → ℂ} {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv f < s.re) (k : ℕ) :
    Summable (fun n : ℕ => ‖LSeries.term f s n‖ * Real.log (n : ℝ) ^ k) := by
  have hsum : LSeriesSummable (LSeries.logMul^[k] f) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hs)
  simpa only [norm_term_logMul_iterate] using (summable_norm_iff.mpr hsum)

open scoped ComplexOrder
open scoped Topology

/-- There is no cancellation in a sum of nonnegative real complex numbers. -/
lemma norm_tsum_of_nonneg {g : ℕ → ℂ} (hg : ∀ n, 0 ≤ g n) (hs : Summable g) :
    ‖∑' n, g n‖ = ∑' n, ‖g n‖ := by
  have hnonneg : 0 ≤ ∑' n, g n := tsum_nonneg hg
  rw [← Complex.re_eq_norm.mpr hnonneg, Complex.re_tsum hs]
  exact tsum_congr fun n => Complex.re_eq_norm.mpr (hg n)

/-- Nonnegative coefficients turn derivative norms into exact logarithmic moments. -/
lemma norm_iteratedDeriv_eq_moment {f : ℕ → ℂ} (hf : 0 ≤ f) {s : ℝ}
    (hs : LSeries.abscissaOfAbsConv f < s) (k : ℕ) :
    ‖iteratedDeriv k (LSeries f) (s : ℂ)‖ =
      ∑' n : ℕ, ‖LSeries.term f (s : ℂ) n‖ * Real.log (n : ℝ) ^ k := by
  have hcoeff (n : ℕ) : 0 ≤ (LSeries.logMul^[k] f) n := by
    rw [logMul_iterate_apply]
    apply mul_nonneg _ (hf n)
    apply pow_nonneg
    simpa only [← Complex.natCast_log, Complex.zero_le_real] using log_nat_nonneg n
  have hsum : LSeriesSummable (LSeries.logMul^[k] f) (s : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hs)
  rw [LSeries_iteratedDeriv k hs, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  change ‖∑' n, LSeries.term (LSeries.logMul^[k] f) (s : ℂ) n‖ = _
  rw [norm_tsum_of_nonneg (fun n => LSeries.term_nonneg (hcoeff n) s) hsum]
  exact tsum_congr fun n => norm_term_logMul_iterate f (s : ℂ) k n

/-- Multiplication by the exponential of a logarithm shifts a Dirichlet exponent. -/
lemma norm_term_shift (f : ℕ → ℂ) (s r : ℝ) (n : ℕ) :
    ‖LSeries.term f ((s - r : ℝ) : ℂ) n‖ =
      ‖LSeries.term f (s : ℂ) n‖ * Real.exp (r * Real.log (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hexp : Real.exp (r * Real.log (n : ℝ)) = (n : ℝ) ^ r := by
      rw [Real.rpow_def_of_pos hnR]
      congr 1
      ring
    simp only [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re]
    rw [Real.rpow_sub hnR, hexp]
    field_simp

/-- A local holomorphic continuation with nonnegative Dirichlet coefficients forces
convergence at every real point to its left within the Taylor disc. -/
theorem summable_of_holomorphic_continuation {f : ℕ → ℂ} (hf : 0 ≤ f)
    {s r R : ℝ} (hs : LSeries.abscissaOfAbsConv f < s) (hr : 0 ≤ r) (hrR : r < R)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball (s : ℂ) R))
    (heq : F =ᶠ[𝓝 (s : ℂ)] LSeries f) :
    LSeriesSummable f ((s - r : ℝ) : ℂ) := by
  have hzdist : ‖((s - r : ℝ) : ℂ) - (s : ℂ)‖ = r := by
    have harg : ((s - r : ℝ) : ℂ) - (s : ℂ) = -(r : ℂ) := by
      push_cast
      ring
    rw [harg, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hz : ((s - r : ℝ) : ℂ) ∈ Metric.ball (s : ℂ) R := by
    simpa only [Metric.mem_ball, dist_eq_norm, hzdist] using hrR
  have htaylor := Complex.hasSum_taylorSeries_on_ball hF hz
  have hnorm := summable_norm_iff.mpr htaylor.summable
  have hmoment (k : ℕ) :
      (∑' n : ℕ, ‖LSeries.term f (s : ℂ) n‖ * (r * Real.log (n : ℝ)) ^ k) =
        r ^ k * ∑' n : ℕ, ‖LSeries.term f (s : ℂ) n‖ * Real.log (n : ℝ) ^ k := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [mul_pow]
    ring
  have hcoeff (k : ℕ) :
      ‖(k.factorial : ℂ)⁻¹ • (((s - r : ℝ) : ℂ) - (s : ℂ)) ^ k •
        iteratedDeriv k F (s : ℂ)‖ =
      (∑' n : ℕ, ‖LSeries.term f (s : ℂ) n‖ * (r * Real.log (n : ℝ)) ^ k) /
        (k.factorial : ℝ) := by
    rw [norm_smul, norm_smul, norm_inv, norm_pow, hzdist,
      heq.iteratedDeriv_eq k, norm_iteratedDeriv_eq_moment hf hs k,
      Complex.norm_natCast, hmoment]
    ring
  have hpower : Summable (fun k : ℕ =>
      (∑' n : ℕ, ‖LSeries.term f (s : ℂ) n‖ * (r * Real.log (n : ℝ)) ^ k) /
        (k.factorial : ℝ)) := hnorm.congr hcoeff
  have hm (k : ℕ) : Summable (fun n : ℕ =>
      ‖LSeries.term f (s : ℂ) n‖ * (r * Real.log (n : ℝ)) ^ k) := by
    have h := (summable_log_moments (s := (s : ℂ)) hs k).mul_left (r ^ k)
    refine h.congr fun n => ?_
    rw [mul_pow]
    ring
  have hexp := summable_weighted_exp_of_moments (fun n => norm_nonneg _)
    (fun n => mul_nonneg hr (log_nat_nonneg n)) hm hpower
  exact summable_norm_iff.mp (hexp.congr fun n => (norm_term_shift f s r n).symm)

end LeanEval.NumberTheory.Lagarias.Landau
