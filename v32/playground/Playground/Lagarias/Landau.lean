import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Positivity and analytic continuation of Dirichlet series

This module develops the positivity argument used in Landau's theorem on the
singularity at a finite abscissa of convergence. It is independent of Robin's
theorems and of the still-incomplete target in `v32/Lagarias.lean`.

The first lemma is the Tonelli step: summability of all nonnegative moments,
together with summability of their exponential generating series, implies
summability of the exponentially weighted original sequence.
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
  have hF : Summable F := (summable_prod_of_nonneg hF0).2 ⟨?_, ?_⟩
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
lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

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

end LeanEval.NumberTheory.Lagarias.Landau
