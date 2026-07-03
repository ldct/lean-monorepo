import Mathlib

open scoped DirectSum

abbrev CPolynomial (R) [Semiring R] := ⨁ i : ℕ, R
abbrev CPolynomial.X {R} [Semiring R] : CPolynomial R := .single 1 1

unsafe instance {R} [Semiring R] [Repr R] : Repr (CPolynomial R) where
  reprPrec x prec :=
    let l := x.support'.unquot.1.sort (· ≤ ·)
    Std.Format.joinSep (l.map fun
      | 0 => repr (x 0)
      | 1 => f!"{repr (x 1)}*X"
      | i => f!"{repr (x i)}*X^{i}") f!" + "

open CPolynomial

#eval (3*X^2 + 1 : CPolynomial Int)

example :
    ∀ p ∈ ({3*X^2, 2*X^3, 3*X + 1} : Finset (CPolynomial Int)), p ≠ 0 := by
  decide


open Polynomial in
example : Polynomial.coeff (0 : ℤ[X]) 0 = 0 := by exact coeff_zero 0
open Polynomial in
example : coeff (1 : ℤ[X]) 0 = 1 := by exact coeff_one_zero
