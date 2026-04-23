import Playground.PrimeSieve.Basic
import Playground.PrimeSieve.Simproc

/-!
# Tests / examples for the prime sieve

The user spends one `decide` to prove `PrimeSieve.Valid N` (the sieve
precompute, `O(N log log N)` in kernel time). After that, every `Nat.Prime k`
question with `k ≤ N` is answered by a kernel-checkable `Bool` lookup.

All examples below avoid `native_decide`; everything is verified by the
kernel.
-/

namespace PrimeSieve

-- Smoke test: the sieve agrees with `Nat.Prime` for small `N`.
example : isPrime 20 2 = true := by decide
example : isPrime 20 4 = false := by decide
example : isPrime 20 17 = true := by decide
example : isPrime 20 15 = false := by decide

-- ============================================================
-- Direct usage (no simproc): the user calls `prime_of_lookup`
-- with a precomputed `Valid N` witness.
-- ============================================================

example : Nat.Prime 7 := by
  have hv : Valid 10 := by decide
  exact prime_of_lookup hv (by decide) (by decide)

example : ¬ Nat.Prime 9 := by
  have hv : Valid 10 := by decide
  exact not_prime_of_lookup hv (by decide) (by decide)

-- ============================================================
-- Simproc usage: one `Valid N` hypothesis collapses many primality goals.
-- ============================================================

example : Nat.Prime 11 ∧ Nat.Prime 13 ∧ ¬ Nat.Prime 15 ∧ Nat.Prime 17 := by
  have hv : Valid 20 := by decide
  simp only [primeSieveSimproc]
  trivial

-- Simproc also handles primality in hypotheses.
example (h : Nat.Prime 9) : False := by
  have hv : Valid 10 := by decide
  simp only [primeSieveSimproc] at h

-- A larger conjunction reusing the same precompute.
example :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧
    ¬ Nat.Prime 1 ∧ ¬ Nat.Prime 4 ∧ ¬ Nat.Prime 6 ∧ ¬ Nat.Prime 8 := by
  have hv : Valid 10 := by decide
  simp only [primeSieveSimproc]
  trivial

end PrimeSieve
