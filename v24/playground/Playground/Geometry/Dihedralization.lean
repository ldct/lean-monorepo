import Mathlib
import Playground.Geometry.SmallGroups.SmallGroups

namespace Dihedralization

inductive MyC2 : Type
  | one
  | neg
  deriving Fintype, DecidableEq

instance : Mul MyC2 where
  mul a b :=
    match a, b with
    | .one, x => x
    | x, .one => x
    | .neg, .neg => .one

instance : One MyC2 where
  one := .one

instance : Neg MyC2 where
  neg a :=
    match a with
    | .one => .neg
    | .neg => .one

instance : Group MyC2 := {
  mul_assoc a b c := by decide +revert
  one_mul := by
    rw [show (1 : MyC2) = .one by rfl]
    decide
  mul_one := by
    rw [show (1 : MyC2) = .one by rfl]
    decide
  inv a := a
  inv_mul_cancel a := by
    decide +revert
}

#eval (1 : MyC2)

structure Dihedralization (G) [CommGroup G] [Fintype G] : Type where
  g : G
  c : MyC2
deriving Fintype, DecidableEq


instance {G} [CommGroup G] [Fintype G] : Coe (MyC2 × G) (Dihedralization G) where
  coe a := { g := a.2, c := a.1 }


-- https://cas.umw.edu/math/files/2011/09/honors_brown.pdf
-- example {G} [CommGroup G] (d : Dihedralization G) : d.x = 0 ∨ d.x = 1 := by
--   fin_cases d.x <;> decide

def act {G} [Inv G] (g : G) (x : MyC2) : G :=
  match x with
  | .one => g
  | .neg => g⁻¹

theorem act_one {G} [Group G] (x : MyC2) : act (1 : G) x = 1 := by
  fin_cases x <;> simp [act]

theorem act_g_one {G} [Group G] (g : G) : act g .one = g := rfl

theorem act_g_neg {G} [Group G] (g : G) : act g .neg = g⁻¹ := rfl

/--
(c₁, g₁) * (c₂, g₂) = (c₁ * c₂, g₁^c₂ * g₂)
you should think of g₁^c₂ = c₂⁻¹ * g₁ * c₂

c*g = (c, 1) * (1, g) = (c, g)

g*c = (1, g) * (c, 1) = (c, g^c)
-/

instance {G} [CommGroup G] : HPow G MyC2 G where
  hPow a b := act a b

instance {G} [CommGroup G] [Fintype G] : Mul (Dihedralization G) :=
  {
    mul a b := {
      c := a.c * b.c
      g := a.g ^ b.c * b.g
    }
  }

theorem mul_eq {G} [CommGroup G] [Fintype G] (a b : Dihedralization G) : a * b = {
  c := a.c * b.c
  g := (act a.g b.c) * b.g
} := rfl

theorem either_one_or_neg (v : MyC2) : v = .one ∨ v = .neg := by
  fin_cases v <;> simp

theorem mul_assoc_helper {G} [CommGroup G] [Fintype G] (a b c : Dihedralization G)
: (a * b) * c = a * (b * c) := by
  simp [mul_eq, act]
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

theorem test1 (a : MyC2) : a * .one = a := by decide +revert
theorem test2 (a : MyC2) : .one * a = a := by decide +revert

instance {G} [CommGroup G] [Fintype G] : Group (Dihedralization G) := {
    mul_assoc a b c := mul_assoc_helper a b c
    one_mul a := by
      simp [one_eq, mul_eq, act_one, test2]
    mul_one a := by
      simp [one_eq, mul_eq, test1]
      rfl
    inv a := { g := (act a.g a.c)⁻¹, c := a.c }
    inv_mul_cancel a:= by
      rw [mul_eq]
      simp
      obtain h1 | h1 := either_one_or_neg a.c
      <;> simp [h1, test1, act_g_one, act_g_neg]
      <;> rfl
  }

abbrev T := Dihedralization (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))

#eval Fintype.card T
#eval Group.CommutingFraction T
#eval Group.FracInvolutions T
#eval ∀ (a : T), a^6 = 1
