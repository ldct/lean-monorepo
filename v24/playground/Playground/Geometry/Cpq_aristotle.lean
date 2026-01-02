/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 616150e2-d673-4664-b448-3e1fddfff26a

The following was proved by Aristotle:

- instance (p q : PNat) (r : ZMod p) [h : Fact (r ^ (q.val) = 1)] : Group (Cpqr p q r)
-/

import Mathlib
import Plausible.Random


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

example (r : ZMod 25) (a b c : Cpqr 25 15 r) (h : r ^ 15 = 1)
: (a * b) * c = a * (b * c) := by
  have h_expand : ∀ a b c : Cpqr 25 15 r,
    (a * b) * c = { Q := (a.Q + b.Q) + c.Q, P :=
    (act 25 15 r ((act 25 15 r a.P b.Q).val + b.P) c.Q).val + c.P } ∧
    a * (b * c) = { Q := a.Q + (b.Q + c.Q), P := (act 25 15 r a.P (b.Q + c.Q)).val +
    ((act 25 15 r b.P c.Q).val + c.P) } := by
    bound
  simp_all [← add_assoc]
  unfold act
  ring_nf
  erw [ZMod.val_add]
  erw [← Nat.mod_add_div (b.Q.val + c.Q.val) 15]
  norm_num [pow_add, pow_mul, h]
  rw [show r ^ ((b.Q.val + c.Q.val) % 15) = r ^ (b.Q.val + c.Q.val) by
    rw [← Nat.mod_add_div (b.Q.val + c.Q.val) 15, pow_add, pow_mul];
    aesop]
  ring

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

theorem inv_eq (p q : PNat) (r : ZMod p) (x : Cpqr p q r) : x⁻¹ = { Q := -x.Q, P := - act p q r x.P (-x.Q) } := rfl

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
    simp [Cpqr.mul_eq, act, show (1 : Cpqr p q r) = ⟨ 0, 0 ⟩ by rfl, inv_eq]
    ring_nf
    rw [mul_assoc, ← pow_add]
    rw [ sub_eq_zero, ZMod.neg_val ];
    split_ifs <;> simp_all +decide [ pow_add, pow_one, pow_mul ];
    rw [ ← pow_add, Nat.sub_add_cancel ( show a.Q.val ≤ q from _ ), h.1, mul_one ];
    exact Nat.le_of_lt ( ZMod.val_lt _ )
}