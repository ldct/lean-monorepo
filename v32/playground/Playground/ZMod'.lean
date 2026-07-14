import Mathlib

def divisibleByNRel (n : ℤ) : Setoid ℤ where
  r a b := n ∣ (a - b)
  iseqv := {
    refl := fun a => by
      rw [sub_self]
      exact dvd_zero n
    symm := fun {a b} hab => by
      have hb_eq : b - a = -(a - b) := by ring
      rw [hb_eq]
      exact hab.neg_right
    trans := fun {a b c} hab hbc => by
      have habc : a - c = (a - b) + (b - c) := by ring
      rw [habc]
      exact dvd_add hab hbc
    }

def ZMod' (n : ℤ) := Quotient (divisibleByNRel n)

instance : HasQuotient ℤ ℤ  where
  Quotient n := Quotient (divisibleByNRel n)

/- The canonical Equiv between `ZMod' n` and `ZMod n` -/
def ZMod'Equiv (n : ℕ) : ZMod' n ≃ ZMod n where
  toFun :=
    Quotient.lift (fun (z : ℤ) => (z : ZMod n)) fun a b hab =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub a b n).2 (dvd_sub_comm.mp hab)
  invFun x := Quotient.mk (divisibleByNRel n) (ZMod.valMinAbs x)
  left_inv :=
    Quotient.ind fun a => by
      dsimp only [Quotient.lift_mk]
      refine Quotient.sound (?_ : (divisibleByNRel n).r _ _)
      show (n : ℤ) ∣ _ - _
      have hcast : (ZMod.valMinAbs (a : ZMod n) : ZMod n) = (a : ZMod n) := ZMod.coe_valMinAbs _
      exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 hcast)
  right_inv := fun x => by
    dsimp only [Quotient.lift_mk]
    exact ZMod.coe_valMinAbs x
