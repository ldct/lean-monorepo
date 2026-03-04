import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.DeriveFintype
import Playground.Geometry.C2
import Playground.Geometry.SmallGroups.GroupProps


namespace Dihedralization
open C2

/-!
This file defines the dihedralization of a commutative group G and proves that it is a group.

References
https://cas.umw.edu/math/files/2011/09/honors_brown.pdf

The main purpose is to construct T3 = Dihedralization (ZMod 3 × ZMod 3), a group of order 18.
-/

structure Dihedralization (G) [CommGroup G] [Fintype G] : Type where
  c : C2
  g : G
deriving Fintype, DecidableEq

def act {G} [Inv G] (g : G) (x : C2) : G :=
  match x with
  | .one => g
  | .neg => g⁻¹

theorem act_one {G} [Group G] (x : C2) : act (1 : G) x = 1 := by
  fin_cases x <;> simp [act]

@[simp]
theorem act_g_one {G} [Group G] (g : G) : act g .one = g := rfl

@[simp]
theorem act_g_neg {G} [Group G] (g : G) : act g .neg = g⁻¹ := rfl

/--
(c₁, g₁) * (c₂, g₂) = (c₁ * c₂, g₁^c₂ * g₂)
you should think of g₁^c₂ = c₂⁻¹ * g₁ * c₂

c*g = (c, 1) * (1, g) = (c, g)

g*c = (1, g) * (c, 1) = (c, g^c)
-/

instance {G} [CommGroup G] : HPow G C2 G where
  hPow a b := act a b

instance {G} [CommGroup G] [Fintype G] : Mul (Dihedralization G) := ⟨
  fun ⟨c₁, g₁⟩ ⟨c₂, g₂⟩ =>
  ⟨ c₁ * c₂, (act g₁ c₂) * g₂ ⟩
⟩

theorem Dihedralization.mul_eq {G} [CommGroup G] [Fintype G] (a b : Dihedralization G)
: a * b = ⟨ a.c * b.c, (act a.g b.c) * b.g ⟩ := rfl

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
  one := ⟨ .one, 1 ⟩,
}

theorem one_eq {G} [CommGroup G] [Fintype G]
: (1 : Dihedralization G) = ⟨ .one, 1 ⟩ := rfl

@[simp] theorem C2.mul_one (a : C2) : a * .one = a := by decide +revert
@[simp] theorem C2.one_mul (a : C2) : .one * a = a := by decide +revert

instance {G} [CommGroup G] [Fintype G] : Group (Dihedralization G) := {
  mul_assoc a b c := mul_assoc_helper a b c
  one_mul a := by
    simp [one_eq, Dihedralization.mul_eq, act_one, C2.one_mul]
  mul_one a := by
    simp [one_eq, Dihedralization.mul_eq, C2.mul_one]
  inv a := { g := (act a.g a.c)⁻¹, c := a.c }
  inv_mul_cancel a:= by
    rw [Dihedralization.mul_eq]
    simp
    obtain h1 | h1 := either_one_or_neg a.c
    <;> simp [h1, act_g_one, act_g_neg]
    <;> rfl
}


end Dihedralization