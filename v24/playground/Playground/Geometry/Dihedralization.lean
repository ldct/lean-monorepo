import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Playground.Geometry.C2
import Playground.Geometry.SmallGroups.GroupProps

/-!
This file defines the dihedralization of a commutative group G and proves that it is a group.

References
https://cas.umw.edu/math/files/2011/09/honors_brown.pdf

The main purpose is to construct T3 = Dihedralization (ZMod 3 × ZMod 3), a group of order 18.
-/

structure Dihedralization (G) [CommGroup G] [Fintype G] : Type where
  g : G
  c : C2
deriving Fintype, DecidableEq

-- An attempt to coercion from C2 × G to Dihedralization G.
-- If successful, we can use the notation (c, g) * (c', g') in proofs, which is more concise.
instance {G} [CommGroup G] [Fintype G] : Coe (C2 × G) (Dihedralization G) where
  coe a := { g := a.2, c := a.1 }

def act {G} [Inv G] (g : G) (x : C2) : G :=
  match x with
  | .one => g
  | .neg => g⁻¹

theorem act_one {G} [Group G] (x : C2) : act (1 : G) x = 1 := by
  fin_cases x <;> simp [act]

theorem act_g_one {G} [Group G] (g : G) : act g .one = g := rfl

theorem act_g_neg {G} [Group G] (g : G) : act g .neg = g⁻¹ := rfl

/--
(c₁, g₁) * (c₂, g₂) = (c₁ * c₂, g₁^c₂ * g₂)
you should think of g₁^c₂ = c₂⁻¹ * g₁ * c₂

c*g = (c, 1) * (1, g) = (c, g)

g*c = (1, g) * (c, 1) = (c, g^c)
-/

instance {G} [CommGroup G] : HPow G C2 G where
  hPow a b := act a b

instance {G} [CommGroup G] [Fintype G] : Mul (Dihedralization G) :=
  {
    mul a b := {
      c := a.c * b.c
      g := a.g ^ b.c * b.g
    }
  }

theorem Dihedralization.mul_eq {G} [CommGroup G] [Fintype G] (a b : Dihedralization G) : a * b = {
  c := a.c * b.c
  g := (act a.g b.c) * b.g
} := rfl

theorem either_one_or_neg (v : C2) : v = .one ∨ v = .neg := by
  fin_cases v <;> simp

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
