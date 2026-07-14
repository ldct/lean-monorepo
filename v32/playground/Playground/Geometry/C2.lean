import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.DeriveFintype


namespace C2

inductive C2 : Type
  | one
  | neg
  deriving Fintype, DecidableEq

instance : Mul C2 where
  mul a b :=
    match a, b with
    | .one, x => x
    | x, .one => x
    | .neg, .neg => .one

instance : One C2 where
  one := .one

instance : Neg C2 where
  neg a :=
    match a with
    | .one => .neg
    | .neg => .one

instance : Group C2 := {
  mul_assoc a b c := by decide +revert
  one_mul := by
    rw [show (1 : C2) = .one by rfl]
    decide
  mul_one := by
    rw [show (1 : C2) = .one by rfl]
    decide
  inv a := a
  inv_mul_cancel a := by
    decide +revert
}


end C2