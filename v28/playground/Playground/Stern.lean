/-
Copyright (c) 2025 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib
-- import LeanTeXMathlib  -- not available in v24

namespace Stern

def D : ℕ → ℕ
  | 0 => 2
  | n + 1 => (D n)^2

#eval D 3


theorem D_recurrence (n : ℕ) : D n = 2 ^ (2 ^ n) := by
  induction n
  case zero =>
    unfold D
    simp
  case succ n IH =>
    rw [D]
    rw [IH]
    group


end Stern