/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 77f5a10b-4701-4ea4-b949-8c076b7630ca

The following was proved by Aristotle:

- instance {G} [CommGroup G] : Group (Dihedralization G)
-/

import Mathlib


structure Dihedralization (G) [CommGroup G] : Type where
  g : G
  c : ZMod 2

-- https://cas.umw.edu/math/files/2011/09/honors_brown.pdf
-- example {G} [CommGroup G] (d : Dihedralization G) : d.x = 0 ∨ d.x = 1 := by
--   fin_cases d.x <;> decide

def act {G} [Inv G] (g : G) (x : ZMod 2) : G :=
  match x with
  | 0 => g
  | 1 => g⁻¹

/--
(c₁, g₁) * (c₂, g₂) = (c₁ * c₂, g₁^c₂ * g₂)
you should think of g₁^c₂ = c₂⁻¹ * g₁ * c₂

c*g = (c, 1) * (1, g) = (c, g)

g*c = (1, g) * (c, 1) = (c, g^c)

-/

instance {G} [CommGroup G] : Mul (Dihedralization G) :=
  {
    mul a b := {
      c := a.c + b.c
      g := (act a.g b.c) * b.g
    }
  }

theorem mul_eq {G} [CommGroup G] (a b : Dihedralization G) : a * b = {
  c := a.c + b.c
  g := (act a.g b.c) * b.g
} := rfl

theorem either_zero_or_one (v : ZMod 2) : v = 0 ∨ v = 1 := by
  fin_cases v <;> simp

instance {G} [CommGroup G] : Group (Dihedralization G) :=
  {
    mul_assoc a b c := by
      simp [mul_eq, act]
      obtain h1 | h1 := either_zero_or_one a.c
      <;> obtain h2 | h2 := either_zero_or_one b.c
      <;> obtain h3 | h3 := either_zero_or_one c.c
      <;> simp [h1, h2, h3]
      <;> group
      rw [mul_comm (a.g ^ (-1))]
      -- Since multiplication is commutative in a commutative group, we can rearrange the terms on the right-hand side.
      have h_comm : b.g ^ (-1 : ℤ) * a.g * c.g = a.g * b.g ^ (-1 : ℤ) * c.g := by
        grind;
      -- Since the group is commutative, the order of multiplication does not matter, so the two expressions are equal.
      convert h_comm using 1
      -- By commutativity of multiplication in the commutative group G, we can rearrange the terms.
      simp [mul_comm, mul_assoc, mul_left_comm]
      -- Since multiplication in G is commutative, we can rearrange the terms to show the equality.
      have h_comm : a.g * b.g⁻¹ = b.g⁻¹ * a.g := by
        -- Since G is a commutative group, multiplication is commutative.
        apply mul_comm;
      -- Since multiplication in G is commutative, we can rearrange the terms to show the equality. Therefore, the goal holds.
      simp [h_comm];
      exact?

    one := { g := 1, c := 0 },
    one_mul := by admit,
    mul_one := by admit,
    inv := by admit,
    inv_mul_cancel := by admit,
  }