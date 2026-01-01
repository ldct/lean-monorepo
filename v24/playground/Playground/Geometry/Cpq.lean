import Mathlib

/--!
This file defines a group parameterised by p, q, and r which is the semidirect product of ZMod p and ZMod q.
-/

#eval IsUnit (5 : ZMod 6)

structure Cpq (p q prim : ℕ) [Fact p.Prime] [Fact q.Prime] : Type where
  r : ZMod q
  g : Units (ZMod q)
deriving Fintype, DecidableEq

def act (p q prim : ℕ) (g : ZMod p) (r : ZMod q) : ZMod p :=
  g.val * r.val * prim

/--
(r₁, g₁) * (r₂, g₂) = (r₁ * r₂, g₁^r₂ * g₂)
you should think of g₁^r₂ = r₂⁻¹ * g₁ * r₂

r*g = (r, 1) * (1, g) = (r, g)

g*r = (1, g) * (r, 1) = (r, g^r)
-/

instance (p q prim : ℕ) [Fact p.Prime] [Fact q.Prime] : Mul (Cpq p q r) :=
  {
    mul a b := {
      r := a.r * b.r
      g := (act p q prim a.g b.r) + b.g
    }
  }

theorem Dihedralization.mul_eq {G} [CommGroup G] [Fintype G] (a b : Dihedralization G) : a * b = {
  c := a.c * b.c
  g := (act a.g b.c) * b.g
} := rfl


theorem mul_assoc_helper {G} [CommGroup G] [Fintype G] (a b c : Dihedralization G)
: (a * b) * c = a * (b * c) := by
  simp [Dihedralization.mul_eq, act]
  obtain h1 | h1 := either_one_or_neg a.c
  <;> obtain h2 | h2 := either_one_or_neg b.c
  <;> obtain h3 | h3 := either_one_or_neg c.c
  <;> simp +decide [h1, h2, h3]
  <;> group
  <;> grind

instance {G} [CommGroup G] [Fintype G] : One (Dihedralization G) := {
  one := { g := 1, c := .one },
}

theorem one_eq {G} [CommGroup G] [Fintype G]
: (1 : Dihedralization G) = { g := 1, c := .one } := rfl

theorem test1 (a : C2) : a * .one = a := by decide +revert
theorem test2 (a : C2) : .one * a = a := by decide +revert

instance {G} [CommGroup G] [Fintype G] : Group (Dihedralization G) := {
    mul_assoc a b c := mul_assoc_helper a b c
    one_mul a := by
      simp [one_eq, Dihedralization.mul_eq, act_one, test2]
    mul_one a := by
      simp [one_eq, Dihedralization.mul_eq, test1]
      rfl
    inv a := { g := (act a.g a.c)⁻¹, c := a.c }
    inv_mul_cancel a:= by
      rw [Dihedralization.mul_eq]
      simp
      obtain h1 | h1 := either_one_or_neg a.c
      <;> simp [h1, test1, act_g_one, act_g_neg]
      <;> rfl
  }

-- A small group of order 18.

-- abbrev T := Dihedralization (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))
-- #eval Fintype.card T
-- #eval Group.CommutingFraction T
-- #eval _root_.Group.FracInvolutions T
-- #eval ∀ (a : T), a^6 = 1
