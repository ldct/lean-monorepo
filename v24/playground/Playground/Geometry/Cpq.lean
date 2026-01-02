import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.DeriveFintype
import Plausible.Random
import Playground.Geometry.SmallGroups.GroupProps

/-!
This file defines a group parameterised by p, q, and r which is the semidirect product of ZMod p and ZMod q
-/

#synth Plausible.Arbitrary (Fin 3)

instance ZMod.Arbitrary {n : Nat} : Plausible.Arbitrary (ZMod (n.succ)) where
  arbitrary := do
    let m ← Plausible.Gen.choose Nat 0 (min (← Plausible.Gen.getSize) n) (Nat.zero_le _)
    return m

instance ZMod.shrinkable {n : Nat} : Plausible.Shrinkable (ZMod (n.succ)) where
  shrink m := [m]

#synth Plausible.SampleableExt (ZMod 3)
#sample (ZMod 3)

structure Cpqr (p q : PNat) (r : ZMod p) : Type where
  P : ZMod p
  Q : ZMod q
deriving Fintype, DecidableEq, Repr

instance Cpqr.Arbitrary (p q : PNat) (r : ZMod p) : Plausible.Arbitrary (Cpqr p q r) where
  arbitrary := do
    let p ← Plausible.Gen.choose Nat 0 (min (← Plausible.Gen.getSize) p) (Nat.zero_le _)
    let q ← Plausible.Gen.choose Nat 0 (min (← Plausible.Gen.getSize) q) (Nat.zero_le _)
    return { P := p, Q := q }

instance Cpqr.shrinkable (p q : PNat) (r : ZMod p) : Plausible.Shrinkable (Cpqr p q r) where
  shrink a := [a]

namespace Cpqr

def act (p q : PNat) (r : ZMod p) (P : ZMod p) (Q : ZMod q) : ZMod p :=
  P * r^(Q.val)

instance (p q : PNat) (r : ZMod p) : Mul (Cpqr p q r) :=
  {
    mul left right := {
      Q := left.Q + right.Q
      P := (act p q r left.P right.Q).val + right.P
    }
  }

theorem Cpqr.mul_eq (p q : PNat) (r : ZMod p) (left right : Cpqr p q r) : left * right = {
  Q := left.Q + right.Q
  P := (act p q r left.P right.Q).val + right.P
} := rfl

example (a b c : Cpqr 8 2 3)
: (a * b) * c = a * (b * c) := by
  native_decide +revert

example (a b c : Cpqr 8 2 5)
: (a * b) * c = a * (b * c) := by
  native_decide +revert

example (a b c : Cpqr 4 4 3)
: (a * b) * c = a * (b * c) := by
  native_decide +revert

-- example (a b c : Cpqr 25 15 6)
-- : (a * b) * c = a * (b * c) := by
--   plausible


theorem mul_assoc_helper (p q : PNat) (r : ZMod p) (a b c : Cpqr p q r) (h : r ^ (q.val) = 1)
: (a * b) * c = a * (b * c) := by
  simp [Cpqr.mul_eq, act];
  have h_sum : (b.Q.val + c.Q.val) % q.val = (b.Q + c.Q).val := by
    grind [ZMod.val_add]
  simp [ add_mul, mul_assoc, ← pow_add ]
  rw [ ← h_sum, ← Nat.mod_add_div ( b.Q.val + c.Q.val ) q.val ]
  simp [ pow_add, pow_mul, h ]
  grind

instance (p q : PNat) (r : ZMod p) : Inv (Cpqr p q r) where
  inv x :=
    { Q := -x.Q
      P := - act p q r x.P (-x.Q) }

theorem Cpq.inv_eq (p q : PNat) (r : ZMod p) (x : Cpqr p q r) : x⁻¹ = { Q := -x.Q, P := - act p q r x.P (-x.Q) } := rfl

instance (p q : PNat) (r : ZMod p) : One (Cpqr p q r) where
  one :=
    { P := 0
      Q := 0 }


example (a : Cpqr 25 15 6)
: a * a⁻¹ = ⟨ 0, 0 ⟩ := by
  -- plausible
  native_decide +revert

-- example
--   (p q : PNat)
--   (r : ZMod p)
--   (h : (r.val) ^ (q.val) = 1)
-- : p + q = q + p := by
--   plausible


instance (p q : PNat) (r : ZMod p) [h : Fact (r ^ (q.val) = 1)] : Group (Cpqr p q r) := {
  mul_assoc a b c := mul_assoc_helper p q r a b c h.out
  one_mul a := by
    simp [Cpqr.mul_eq, act, show (1 : Cpqr p q r) = ⟨ 0, 0 ⟩ by rfl]
  mul_one a := by
    simp [Cpqr.mul_eq, act, show (1 : Cpqr p q r) = ⟨ 0, 0 ⟩ by rfl]
  inv_mul_cancel a:= by
    simp [Cpqr.mul_eq, act, show (1 : Cpqr p q r) = ⟨ 0, 0 ⟩ by rfl, Cpq.inv_eq]
    ring_nf
    rw [mul_assoc, ← pow_add]
    rw [ sub_eq_zero, ZMod.neg_val ];
    split_ifs <;> simp_all +decide [ pow_add ]
    rw [ ← pow_add, Nat.sub_add_cancel ( show a.Q.val ≤ q from _ ), h.1, mul_one ];
    exact Nat.le_of_lt ( ZMod.val_lt _ )
}


-- instance : Fact ((3 : ZMod (8:PNat)) ^ (2:PNat).val = 1) := ⟨(by decide)⟩
-- instance : Fact ((5 : ZMod (8:PNat)) ^ (2:PNat).val = 1) := ⟨(by decide)⟩
-- #eval Finset.card { x : Cpqr 8 2 5 | finOrderOf x = 2 }
