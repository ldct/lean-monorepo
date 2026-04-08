import Mathlib

/-
Theorems and definitions from https://tangentmeasure.com/paper/divalg3.pdf
-/

#check SMul

-- R is a n-dimensional real vector space
structure RealAlgebra (n : ℕ) (A : Type*) extends Mul A, SMul ℝ A, Add A where
  toVec (a : A) : (Fin n) → ℝ
  mul₁ (l : ℝ) (x y z : A) : x * (l • y + z) = l • (x * y) + x * z
  mul₂ (l : ℝ) (x y z : A) : (l • x + y) * z = l • (x * z) + y * z

instance : RealAlgebra 1 ℝ where
  toVec r := fun _ => r
  mul₁ l x y z := by
    simp only [smul_eq_mul]
    grind
  mul₂ l x y z := by
    simp only [smul_eq_mul]
    grind

noncomputable instance : RealAlgebra 2 ℂ where
  toVec z := fun i => match i with
    | 0 => z.re
    | 1 => z.im
  mul₁ l x y z := by
    rw [show l • y = l * y by rfl]
    rw [show l • (x * y) = l * (x * y) by rfl]
    grind
  mul₂ l x y z := by
    rw [show l • x = l * x by rfl]
    rw [show l • (x * z) = l * (x * z) by rfl]
    grind

structure WeirdMul where
  val : ℂ

open ComplexConjugate

instance : Mul WeirdMul where
  mul x y := {
    val := conj (x.val * y.val)
  }

noncomputable instance : RealAlgebra 4 (Quaternion ℝ) where
  toVec q := fun i => match i with
    | 0 => q.re
    | 1 => q.imI
    | 2 => q.imJ
    | 3 => q.imK
  mul₁ l x y z := by
    simp only [← Quaternion.coe_mul_eq_smul]
    rw [Quaternion.coe_commutes _ y, Quaternion.coe_commutes l _]
    grind
  mul₂ l x y z := by
    simp only [← Quaternion.coe_mul_eq_smul]
    grind
