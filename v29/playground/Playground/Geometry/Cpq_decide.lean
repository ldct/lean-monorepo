import Mathlib
import Plausible.Random
import Playground.Geometry.SmallGroups.GroupProps


namespace Cpq_decide

structure Cpqr (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) : Type where
  P : ZMod p
  Q : ZMod q
  h := h
deriving Repr

def act (p q : PNat) (r : ZMod p) (P : ZMod p) (Q : ZMod q) : ZMod p :=
  P * r^(Q.val)

instance (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) : Mul (Cpqr p q r h) :=
  {
    mul left right := {
      Q := left.Q + right.Q
      P := (act p q r left.P right.Q).val + right.P
      h := left.h
    }
  }

theorem Cpqr.mul_eq (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) (left right : Cpqr p q r h) : left * right = {
  Q := left.Q + right.Q
  P := (act p q r left.P right.Q).val + right.P,
  h := left.h
} := rfl

theorem mul_assoc_helper (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) (a b c : Cpqr p q r h)
: (a * b) * c = a * (b * c) := by
  simp [Cpqr.mul_eq, act];
  have h_sum : (b.Q.val + c.Q.val) % q.val = (b.Q + c.Q).val := by
    grind [ZMod.val_add]
  simp [ add_mul, mul_assoc, ← pow_add ]
  rw [ ← h_sum, ← Nat.mod_add_div ( b.Q.val + c.Q.val ) q.val ]
  simp [ pow_add, pow_mul, a.h ]
  grind

instance (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) : Inv (Cpqr p q r h) where
  inv x :=
    { Q := -x.Q
      P := - act p q r x.P (-x.Q)
      h := x.h
    }

theorem inv_eq (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) (x : Cpqr p q r h) : x⁻¹ = { Q := -x.Q, P := - act p q r x.P (-x.Q), h := x.h } := rfl

instance (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) : One (Cpqr p q r h) where
  one :=
    { P := 0
      Q := 0
      h := h
    }

instance (p q : PNat) (r : ZMod p) (h : (r ^ (q.val) = 1)) : Group (Cpqr p q r h) := {
  mul_assoc a b c := mul_assoc_helper p q r h a b c
  one_mul a := by
    simp [Cpqr.mul_eq, act, show (1 : Cpqr p q r h) = ⟨ 0, 0, h ⟩ by rfl]
  mul_one a := by
    simp [Cpqr.mul_eq, act, show (1 : Cpqr p q r h) = ⟨ 0, 0, h ⟩ by rfl]
  inv_mul_cancel a:= by
    simp [Cpqr.mul_eq, act, show (1 : Cpqr p q r h) = ⟨ 0, 0, h ⟩ by rfl, inv_eq]
    ring_nf
    rw [mul_assoc, ← pow_add]
    rw [ sub_eq_zero, ZMod.neg_val ];
    split_ifs <;> simp_all +decide [ pow_add ]
    rw [ ← pow_add, Nat.sub_add_cancel ( show a.Q.val ≤ q from _ ), h, mul_one ];
    exact Nat.le_of_lt ( ZMod.val_lt _ )
}

#synth Group (Cpqr 8 2 3 (by decide))


end Cpq_decide