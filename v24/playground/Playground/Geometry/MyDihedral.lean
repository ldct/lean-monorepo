import Mathlib

#check DihedralGroup

-- Is it possible to define the dihedral group with a single constructor naturally

inductive MyDihedralGroup (n : ℕ) : Type
  | sr : ZMod 2 → ZMod n → MyDihedralGroup n
  deriving DecidableEq

namespace MyDihedralGroup

variable {n : ℕ}

def mul : MyDihedralGroup n → MyDihedralGroup n → MyDihedralGroup n
  | sr a i, sr b j =>
      if b = 0 then
        sr (a + b) (i + j)
      else
        sr (a + b) (j - i)
