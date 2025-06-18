/-
Copyright (c) 2025 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib
import LeanTeXMathlib

def D : ℕ → ℕ
  | 0 => 2
  | n + 1 => (D n)^2

#eval D 3

latex_pp_app_rules (const := D)
  | _, #[n] => do
    let n ← LeanTeX.latexPP n
    return "D_{" ++ n ++ "}"

theorem D_recurrence (n : ℕ) : D n = 2 ^ (2 ^ n) := by
  induction n
  case zero =>
    unfold D
    simp
  case succ n IH =>
    rw [D]
    rw [IH]
    group
