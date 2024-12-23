import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

inductive MyDihedralGroup (n : ℕ) : Type
  | r : ZMod n → MyDihedralGroup n
  | sr : ZMod n → MyDihedralGroup n
  deriving DecidableEq

namespace MyDihedralGroup

private def mul : MyDihedralGroup n → MyDihedralGroup n → MyDihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)


/-- The group structure on `DihedralGroup n`.
-/
instance : Group (MyDihedralGroup n) where
  mul := mul
  mul_assoc := by
    rintro (a | a) (b | b) (c | c)
    simp [(· * ·), mul]
    repeat sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  inv_mul_cancel := sorry
