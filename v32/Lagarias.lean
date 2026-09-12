import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
Lagarias' elementary criterion for the Riemann hypothesis.

Source: https://lean-lang.org/eval/problems/riemann_hypothesis_iff_lagarias_elementary_criterion/
-/

namespace LeanEval.NumberTheory

open scoped ArithmeticFunction.sigma

def LagariasElementaryCriterion : Prop :=
  ∀ n : ℕ,
    0 < n →
      ((σ 1 n : ℕ) : ℝ) ≤
        (harmonic n : ℝ) +
          Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis ↔ LagariasElementaryCriterion := by
  sorry

end LeanEval.NumberTheory
