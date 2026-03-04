
namespace IsSquare_refutation_aristotle

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 05ca9fa8-5d44-43df-81e4-cb011a3f62c1

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example : ¬IsSquare (X ^ 2 + 1 : ℤ[X])
-/

import Mathlib


open Polynomial

example : ¬IsSquare (X ^ 2 + 1 : ℤ[X]) := by
  rintro ⟨ p, hp ⟩;
  -- If $p$ is a polynomial with integer coefficients such that $p^2 = X^2 + 1$, then $p$ must be linear.
  have h_linear : ∃ a b : ℤ, p = Polynomial.C a * Polynomial.X + Polynomial.C b := by
    have := congr_arg Polynomial.natDegree hp; norm_num [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] at this;
    exact ⟨ p.coeff 1, p.coeff 0, Polynomial.eq_X_add_C_of_natDegree_le_one <| by rw [ Polynomial.natDegree_mul ( by aesop_cat ) ( by aesop_cat ) ] at this; linarith ⟩;
  rcases h_linear with ⟨ a, b, rfl ⟩ ; have h₁ := congr_arg ( Polynomial.eval 0 ) hp ; have h₂ := congr_arg ( Polynomial.eval ( -1 ) ) hp ; have h₃ := congr_arg ( Polynomial.eval 1 ) hp ; norm_num at * ; nlinarith [ show a > -2 by nlinarith, show a < 2 by nlinarith ] ;

end IsSquare_refutation_aristotle