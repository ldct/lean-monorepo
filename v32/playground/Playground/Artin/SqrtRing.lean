/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji
-/
import Mathlib

/-!
# A tactic for elementary real square-root identities

`sqrt_ring` proves polynomial identities involving `Real.sqrt`. It first normalizes the
surrounding ring expression, replaces products and squares of nonnegative square roots,
and runs `norm_num` and `ring`. If that does not close the goal, it also tries squaring
both sides when `positivity` can prove that both are nonnegative.

This is intended for concrete radical calculations, not as a decision procedure for every
identity of algebraic real numbers.
-/

open Real

namespace SqrtRing

open Lean Meta Qq in
simproc_decl reduceSqrtPow ((Real.sqrt _) ^ _) := fun e => do
  let ⟨.zero, ~q(ℝ), e⟩ ← inferTypeQ' e | return .continue
  match e with
  | ~q((Real.sqrt $x) ^ ($n : ℕ)) =>
      let some k := n.nat? | return .continue
      if k < 3 then return .continue
      let hExpr ← mkDecideProof q((2 : ℕ) ≤ $n)
      let h : Q((2 : ℕ) ≤ $n) := hExpr
      return .done {
        expr := q((Real.sqrt $x) ^ ($n - 2) * (Real.sqrt $x) ^ 2)
        proof? := some q((pow_sub_mul_pow (Real.sqrt $x) $h).symm) }
  | _ => return .continue

lemma sqrt_mul_sqrt_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : √x * √y = √(x * y) :=
  (Real.sqrt_mul hx y).symm

lemma sq_sqrt_of_nonneg {x : ℝ} (hx : 0 ≤ x) : √x ^ 2 = x :=
  Real.sq_sqrt hx

end SqrtRing

/--
Close elementary polynomial identities between concrete real square-root expressions.

Besides direct ring normalization, the tactic tries squaring once when both sides are
provably nonnegative. For example, it proves both `√6 = √2 * √3` and `√8 = 2 * √2`.
-/
macro "sqrt_ring" : tactic =>
  `(tactic|
    first
    | (ring_nf (ifUnchanged := .silent) <;>
        simp (config := { failIfUnchanged := false }) (disch := positivity) only
          [SqrtRing.reduceSqrtPow, SqrtRing.sq_sqrt_of_nonneg, Nat.reduceSub] <;>
        ring_nf (ifUnchanged := .silent) <;>
        simp (config := { failIfUnchanged := false }) (disch := positivity) only
          [SqrtRing.reduceSqrtPow, SqrtRing.sq_sqrt_of_nonneg,
            SqrtRing.sqrt_mul_sqrt_of_nonneg, Nat.reduceSub] <;>
        norm_num <;> ring
       done)
    | (apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
       ring_nf (ifUnchanged := .silent) <;>
        simp (config := { failIfUnchanged := false }) (disch := positivity) only
          [SqrtRing.reduceSqrtPow, SqrtRing.sq_sqrt_of_nonneg, Nat.reduceSub] <;>
        ring_nf (ifUnchanged := .silent) <;>
        simp (config := { failIfUnchanged := false }) (disch := positivity) only
          [SqrtRing.reduceSqrtPow, SqrtRing.sq_sqrt_of_nonneg,
            SqrtRing.sqrt_mul_sqrt_of_nonneg, Nat.reduceSub] <;>
        norm_num <;> ring
       done))

section Tests

example : √6 = √2 * √3 := by
  sqrt_ring

example : 2 * √6 = (√2 + √3) ^ 2 - 5 := by
  sqrt_ring

example : √8 = 2 * √2 := by
  sqrt_ring

example : √2 * √8 = 4 := by
  sqrt_ring

example : (√5 - √2) * (√5 + √2) = 3 := by
  sqrt_ring

example : (√2 + √3) ^ 4 = 49 + 20 * √6 := by
  sqrt_ring

example : √2 ^ 6 = 8 := by
  sqrt_ring

example : √(3 + 2 * √2) = 1 + √2 := by
  sqrt_ring

example : √50 / 5 = √2 := by
  sqrt_ring

end Tests
