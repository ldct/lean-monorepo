import Mathlib

open Polynomial

#check Polynomial.ring

noncomputable def r : ℤ[X] := X
noncomputable def s : ℤ[X] := X + 1

example : r + s = 2 * X + 1 := by
  simp [r, s]
  ring

noncomputable def p : (ZMod 3)[X] := X ^ 2 + 2 * X + 1
noncomputable def q : (ZMod 3)[X] := X ^ 3 + X + 2

example : p + q = X^3 + X^2 := by grind [p, q]

example : p * q = X^5 + 2 * X^4 + 2 * X^3 + X^2 + 2 * X + 2 := by grind [p, q]

-- def IsSquare {R} [CommRing R] (a : R) : Prop := ∃ b, b ^ 2 = a

example : IsSquare (X ^ 2 + 1 : (ZMod 2)[X]) := by
  use X + 1
  grind

example : ¬IsSquare (X ^ 2 + 1 : ℤ[X]) := by sorry
