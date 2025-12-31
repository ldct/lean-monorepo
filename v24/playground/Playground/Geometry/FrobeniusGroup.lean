import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Playground.Geometry.SmallGroups.GroupProps

@[ext]
structure FrobeniusGroup (p : ℕ) [Fact p.Prime] : Type where
  b : (ZMod p)ˣ
  a : ZMod p
deriving Fintype, DecidableEq

variable {p : ℕ} [Fact p.Prime]

def FrobeniusGroup.mul (x y : FrobeniusGroup p) : FrobeniusGroup p :=
  {
    b := x.b * y.b
    a := y.b * x.a + y.a
  }

instance : Mul (FrobeniusGroup p) := ⟨FrobeniusGroup.mul⟩

def FrobeniusGroup.one : FrobeniusGroup p := { b := 1, a := 0 }

instance : One (FrobeniusGroup p) := ⟨FrobeniusGroup.one⟩

def FrobeniusGroup.inv (x : FrobeniusGroup p) : FrobeniusGroup p :=
  { b := x.b⁻¹, a := - (x.b⁻¹ * x.a) }

instance : Inv (FrobeniusGroup p) := ⟨FrobeniusGroup.inv⟩

theorem FrobeniusGroup.mul_def (x y : FrobeniusGroup p) :
  x * y = { b := x.b * y.b, a := y.b * x.a + y.a } := rfl

theorem FrobeniusGroup.mul_assoc {p : ℕ} [Fact p.Prime] (x y z : FrobeniusGroup p) :
  (x * y) * z = x * (y * z) := by
  have h_mul : ∀ x y : FrobeniusGroup p, x * y = ⟨x.b * y.b, y.b * x.a + y.a⟩ := by
    exact fun x y ↦ rfl
  simp [ h_mul ]
  grind

theorem FrobeniusGroup.one_mul {p : ℕ} [Fact p.Prime] (x : FrobeniusGroup p) :
  1 * x = x := by
  have : (1 : FrobeniusGroup p) * x = { b := 1 * x.b, a := x.b * 0 + x.a } := rfl
  simp_all

theorem FrobeniusGroup.mul_one {p : ℕ} [Fact p.Prime] (x : FrobeniusGroup p) :
  x * 1 = x := by
  rw [show (1 : FrobeniusGroup p) = { b := 1, a := 0 } by rfl]
  simp [mul_def]

theorem FrobeniusGroup.inv_mul_cancel {p : ℕ} [Fact p.Prime] (x : FrobeniusGroup p) :
  x⁻¹ * x = 1 := by
  have h_mul : x⁻¹ * x = { b := x.b⁻¹ * x.b, a := x.b • (- (x.b⁻¹ • x.a)) + x.a } := rfl
  rw [h_mul]
  rw [_root_.inv_mul_cancel]
  rw [smul_neg]
  rw [smul_inv_smul, neg_add_cancel]
  rfl

instance {p : ℕ} [Fact p.Prime] : Group (FrobeniusGroup p) where
  mul_assoc := FrobeniusGroup.mul_assoc
  one_mul := FrobeniusGroup.one_mul
  mul_one := FrobeniusGroup.mul_one
  inv_mul_cancel := FrobeniusGroup.inv_mul_cancel


-- A small group of order 20.

-- abbrev T := @FrobeniusGroup 5 (Fact.mk (by decide : Nat.Prime 5))
-- #eval Fintype.card T
-- #eval Group.CommutingFraction T
-- #eval _root_.Group.FracInvolutions T
-- #eval ∀ (a : T), a^6 = 1
