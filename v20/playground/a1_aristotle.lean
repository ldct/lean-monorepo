/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Your Lean code is run in a custom environment, which uses these headers:

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

The following was proved by Aristotle:

- example {G : Type} [Group G] (hG : IsAbelian G) (n : ℤ) : Subgroup G
-/

import Mathlib


def IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

example {G : Type} [Group G] (hG : IsAbelian G) (n : ℤ) : Subgroup G := {
  carrier := { a | a^n = 1 }
  mul_mem' := by
    have : ∀ x y : G, ∀ m : ℕ, (x * y)^m = x^m * y^m := by
      intro x y m
      induction m with
      | zero =>
        simp
      | succ m IH =>
        simp [pow_succ, IH]
        rw [← mul_assoc, hG _ x, ← mul_assoc, hG x]
        group
    cases' Int.eq_nat_or_neg n with hn hn ; aesop


  one_mem' := by
    simp +decide [ zpow_one ]
  inv_mem' := by
    aesop
}