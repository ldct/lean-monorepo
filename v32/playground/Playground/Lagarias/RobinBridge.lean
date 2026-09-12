import Playground.Lagarias.Bounds
import Playground.Lagarias.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The elementary reduction to Robin's analytic estimates

All analytic inputs below are explicit hypotheses, not axioms or proved facts.
This module proves the assembly step in Lagarias' argument; it does not prove
Robin's divisor-sum bound or his oscillation theorem, and therefore does not
complete the RH equivalence in `v32/Lagarias.lean`.
-/

namespace LeanEval.NumberTheory.Lagarias

open scoped ArithmeticFunction.sigma

/-- Cofinal positive Robin oscillations give cofinal strict violations of the
Lagarias inequality. This theorem is independent of the Riemann hypothesis. -/
theorem cofinal_counterexamples_of_robin_oscillation {C β : ℝ}
    (hC : 0 < C) (hβ : β < 1)
    (hOsc : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      robinBound n +
          C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β ≤
        ((σ 1 n : ℕ) : ℝ)) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ rhs n < ((σ 1 n : ℕ) : ℝ) := by
  intro N
  obtain ⟨M, hM⟩ := exists_threshold_error_lt_oscillation hC hβ 7
  obtain ⟨n, hn, hSigma⟩ := hOsc (max N (max 27 M))
  have hnN : N ≤ n := (le_max_left N (max 27 M)).trans hn
  have hn27 : 27 ≤ n := (le_max_left 27 M).trans ((le_max_right N (max 27 M)).trans hn)
  have hnM : M ≤ n := (le_max_right 27 M).trans ((le_max_right N (max 27 M)).trans hn)
  refine ⟨n, hnN, ?_⟩
  calc
    rhs n ≤ robinBound n + 7 * (n : ℝ) / Real.log (n : ℝ) :=
      rhs_le_robinBound_add_error hn27
    _ < robinBound n +
        C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β :=
      add_lt_add_left (hM n hnM) _
    _ ≤ ((σ 1 n : ℕ) : ℝ) := hSigma

/-- The finite check through 5040 and Robin's upper bound on the remaining
integers together imply the elementary inequality for every positive integer. -/
theorem pointwise_inequality_of_finite_and_robin
    (hFinite : ∀ n : ℕ, 0 < n → n ≤ 5040 → ((σ 1 n : ℕ) : ℝ) ≤ rhs n)
    (hRobin : ∀ n : ℕ, 5041 ≤ n → ((σ 1 n : ℕ) : ℝ) ≤ robinBound n) :
    ∀ n : ℕ, 0 < n → ((σ 1 n : ℕ) : ℝ) ≤ rhs n := by
  intro n hn
  by_cases hsmall : n ≤ 5040
  · exact hFinite n hn hsmall
  · exact (hRobin n (by omega)).trans (robinBound_lt_rhs (by omega : 3 ≤ n)).le

/-- This implication isolates the genuinely analytic use of failure of RH. -/
theorem riemannHypothesis_of_pointwise_inequality_of_oscillation
    (hOscillation : ¬ RiemannHypothesis →
      ∃ C β : ℝ, 0 < C ∧ β < 1 ∧
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
          robinBound n +
              C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β ≤
            ((σ 1 n : ℕ) : ℝ))
    (hCriterion : ∀ n : ℕ, 0 < n → ((σ 1 n : ℕ) : ℝ) ≤ rhs n) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨C, β, hC, hβ, hOsc⟩ := hOscillation hRH
  obtain ⟨n, hn, hCounterexample⟩ :=
    cofinal_counterexamples_of_robin_oscillation hC hβ hOsc 1
  exact (not_lt_of_ge (hCriterion n (by omega))) hCounterexample

/-- Conditional assembly, deliberately retaining both unproved Robin inputs
and the finite check as hypotheses. This is not the requested final theorem. -/
theorem riemannHypothesis_iff_pointwise_inequality_of_robin_inputs
    (hFinite : ∀ n : ℕ, 0 < n → n ≤ 5040 → ((σ 1 n : ℕ) : ℝ) ≤ rhs n)
    (hRobin : RiemannHypothesis →
      ∀ n : ℕ, 5041 ≤ n → ((σ 1 n : ℕ) : ℝ) ≤ robinBound n)
    (hOscillation : ¬ RiemannHypothesis →
      ∃ C β : ℝ, 0 < C ∧ β < 1 ∧
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
          robinBound n +
              C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β ≤
            ((σ 1 n : ℕ) : ℝ)) :
    RiemannHypothesis ↔ (∀ n : ℕ, 0 < n → ((σ 1 n : ℕ) : ℝ) ≤ rhs n) := by
  constructor
  · intro hRH
    exact pointwise_inequality_of_finite_and_robin hFinite (hRobin hRH)
  · exact riemannHypothesis_of_pointwise_inequality_of_oscillation hOscillation

end LeanEval.NumberTheory.Lagarias
