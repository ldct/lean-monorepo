import Mathlib
import Playground.Geometry.Chapter_1_1

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/-
Instead of defining the dihedral group as the symmetry group of a regular n-gon, we use exercise 4 as the definition.
-/
inductive MyDihedralGroup (n : ℕ) : Type
  | r : ZMod n → MyDihedralGroup n
  | sr : ZMod n → MyDihedralGroup n
  deriving DecidableEq

namespace MyDihedralGroup
open Chapter_1_1

def mul {n : ℕ} : MyDihedralGroup n → MyDihedralGroup n → MyDihedralGroup n
  | .r i, .r j => .r (i + j)
  | .r i, .sr j => .sr (j - i)
  | .sr i, .r j => .sr (i + j)
  | .sr i, .sr j => .r (j - i)

/-- The inverse of an element of the dihedral group.
-/
def inv {n : ℕ} : MyDihedralGroup n → MyDihedralGroup n
  | .r i => .r (-i)
  | .sr i => .sr i

instance instOne {n : ℕ} : One (MyDihedralGroup n) where
  one := .r 0

lemma one_eq {n : ℕ} : (1 : MyDihedralGroup n) = .r 0 := by rfl

instance instMul {n : ℕ} : Mul (MyDihedralGroup n) where
  mul := mul

@[simp]
theorem r_mul_r {n : ℕ} (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl

@[simp]
theorem r_mul_sr {n : ℕ} (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl

@[simp]
theorem sr_mul_r {n : ℕ} (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl

@[simp]
theorem sr_mul_sr {n : ℕ} (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl

instance instInv {n : ℕ} : Inv (MyDihedralGroup n) where
  inv := inv

@[simp]
lemma inv_r {n : ℕ} (i : ZMod n) : (r i)⁻¹ = r (-i) := rfl

@[simp]
lemma inv_sr {n : ℕ} (i : ZMod n) : (sr i)⁻¹ = sr i := rfl

instance instMyGroup {n : ℕ} : MyGroup (MyDihedralGroup n) where
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp <;> grind
  one := .r 0
  one_mul := by
    rintro (a | a) <;> simp [one_eq]
  mul_one := by
    rintro (a | a) <;> simp [one_eq]
  inv_mul_cancel := by
    rintro (a | a) <;> simp [one_eq]
  mul_inv_cancel := by
    rintro (a | a) <;> simp [one_eq]

/-
TODO - all of exercise 1
-/
example : MyGroup.orderOf (r 1 : MyDihedralGroup 3) = 3 := by
  apply MyGroup.orderOf_of_hasFiniteOrder_spec
  · norm_num
  <;> sorry



end MyDihedralGroup
