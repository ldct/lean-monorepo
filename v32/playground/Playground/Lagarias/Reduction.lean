import Playground.Lagarias.FiniteRange
import Playground.Lagarias.Oscillation
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Reduction of the Lagarias equivalence to the two Robin theorems

This file is a conditional assembly, NOT a completed proof of the target in
`v32/Lagarias.lean`. Both analytic-number-theory inputs are explicit arguments.
They must be proved from Mathlib's actual `RiemannHypothesis`; neither is an axiom.

Reference: Lagarias, arXiv:math/0008177, Propositions 3.1 and 3.2, and the proof
of Theorem 1.1. The finite range, elementary comparisons, and domination of the
oscillation error are supplied by the preceding modules.
-/

namespace LeanEval.NumberTheory.Lagarias

open scoped ArithmeticFunction.sigma

/-- The arithmetic conclusion of Robin's RH-conditional upper bound. -/
def RobinUpperBound : Prop :=
  ∀ n : ℕ, 5041 ≤ n → ((σ 1 n : ℕ) : ℝ) ≤ robinBound n

/-- The arithmetic conclusion of Robin's quantitative oscillation theorem. -/
def RobinOscillation : Prop :=
  ∃ C beta : ℝ, 0 < C ∧ 0 < beta ∧ beta < 1 / 2 ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      robinBound n + C * (n : ℝ) * Real.log (Real.log (n : ℝ)) /
        Real.log (n : ℝ) ^ beta ≤ ((σ 1 n : ℕ) : ℝ)

/-- The forward elementary reduction, including every exceptional integer. -/
theorem criterion_of_robin_upper_bound (hRobin : RobinUpperBound) :
    ∀ n : ℕ, 0 < n → ((σ 1 n : ℕ) : ℝ) ≤ rhs n := by
  intro n hn
  by_cases hsmall : n ≤ 5040
  · exact FiniteCertificates.le_bound_of_le_5040 n hn hsmall
  · exact (hRobin n (by omega)).trans (robinBound_lt_rhs (by omega : 3 ≤ n)).le

/-- Quantitative oscillation gives arbitrarily large failures of the elementary inequality. -/
theorem counterexamples_of_robin_oscillation_assertion (hRobin : RobinOscillation) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ rhs n < ((σ 1 n : ℕ) : ℝ) := by
  rcases hRobin with ⟨C, beta, hC, hbeta0, hbeta, hosc⟩
  exact counterexamples_of_robin_oscillation hC hbeta.le hosc

/-- Conditional assembly of the original mathematical statement.

The two hypotheses below are the remaining analytic proof obligations. A proof
of this theorem is NOT a proof of the unconditional Lagarias equivalence.
-/
theorem riemann_hypothesis_iff_criterion_of_robin_theorems
    (hforward : RiemannHypothesis → RobinUpperBound)
    (hoscillation : ¬ RiemannHypothesis → RobinOscillation) :
    RiemannHypothesis ↔
      ∀ n : ℕ, 0 < n → ((σ 1 n : ℕ) : ℝ) ≤
        (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  constructor
  · intro hRH
    exact criterion_of_robin_upper_bound (hforward hRH)
  · intro hcriterion
    by_contra hnot
    obtain ⟨n, hn, hfail⟩ :=
      counterexamples_of_robin_oscillation_assertion (hoscillation hnot) 1
    exact (not_lt_of_ge (hcriterion n (by omega))) hfail

end LeanEval.NumberTheory.Lagarias
