import Mathlib

namespace LADRDW

@[ext]
structure Complex where
  re : ℝ
  im : ℝ

instance : Add Complex where
  add x y := {
    re := x.re + y.re
    im := x.im + y.im
  }

lemma Complex.add_eq (x y : Complex) : x + y = {
  re := x.re + y.re
  im := x.im + y.im
} := by rfl

instance : Mul Complex where
  mul x y := {
    re := x.re * y.re - x.im * y.im
    im := x.re * y.im + x.im * y.re
  }

lemma Complex.mul_eq (x y : Complex) : x * y = {
  re := x.re * y.re - x.im * y.im
  im := x.re * y.im + x.im * y.re
} := by rfl

-- Example 1.2, done by definition of multiplication
example := calc
  (Complex.mk 2 3) * (Complex.mk 4 5) = Complex.mk (2*4 - 3*5) (2*5 + 3*4) := Complex.mul_eq _ _
  _ = Complex.mk (-7) 22 := by congr <;> norm_num

instance : Zero Complex := ⟨⟨0, 0⟩⟩
instance : One Complex := ⟨⟨1, 0⟩⟩
instance : Neg Complex := ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp] lemma Complex.zero_re : (0 : Complex).re = 0 := rfl
@[simp] lemma Complex.zero_im : (0 : Complex).im = 0 := rfl
@[simp] lemma Complex.one_re : (1 : Complex).re = 1 := rfl
@[simp] lemma Complex.one_im : (1 : Complex).im = 0 := rfl
@[simp] lemma Complex.neg_re (z : Complex) : (-z).re = -z.re := rfl
@[simp] lemma Complex.neg_im (z : Complex) : (-z).im = -z.im := rfl
@[simp] lemma Complex.add_re (x y : Complex) : (x + y).re = x.re + y.re := rfl
@[simp] lemma Complex.add_im (x y : Complex) : (x + y).im = x.im + y.im := rfl
@[simp] lemma Complex.mul_re (x y : Complex) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma Complex.mul_im (x y : Complex) : (x * y).im = x.re * y.im + x.im * y.re := rfl

def Complex.normSq (z : Complex) : ℝ := z.re * z.re + z.im * z.im

lemma Complex.normSq_ne_zero {z : Complex} (h : z ≠ 0) : z.normSq ≠ 0 := by
  obtain ⟨a, b⟩ := z
  intro heq
  apply h
  have hsq : a * a + b * b = 0 := heq
  have ha : a = 0 := by nlinarith [mul_self_nonneg a, mul_self_nonneg b]
  have hb : b = 0 := by nlinarith [mul_self_nonneg a, mul_self_nonneg b]
  ext
  · exact ha
  · exact hb

noncomputable instance : Inv Complex :=
  ⟨fun z => ⟨z.re / z.normSq, -z.im / z.normSq⟩⟩

@[simp] lemma Complex.inv_re (z : Complex) : z⁻¹.re = z.re / z.normSq := rfl
@[simp] lemma Complex.inv_im (z : Complex) : z⁻¹.im = -z.im / z.normSq := rfl

noncomputable instance : Field Complex where
  add := (· + ·)
  add_assoc _ _ _ := by ext <;> simp <;> ring
  zero := 0
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  add_comm _ _ := by ext <;> simp <;> ring
  neg := Neg.neg
  neg_add_cancel _ := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul := (· * ·)
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring
  one := 1
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  inv := Inv.inv
  exists_pair_ne := ⟨0, 1, fun h => by
    have h1 : (0 : Complex).re = (1 : Complex).re := by rw [h]
    rw [Complex.zero_re, Complex.one_re] at h1
    exact zero_ne_one h1⟩
  mul_inv_cancel z hz := by
    have hn : z.re * z.re + z.im * z.im ≠ 0 := Complex.normSq_ne_zero hz
    have h : z.normSq = z.re * z.re + z.im * z.im := rfl
    have hn2 : z.re ^ 2 + z.im ^ 2 ≠ 0 := by rw [sq, sq]; exact hn
    ext
    · simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.one_re, h]
      field_simp
      ring
    · simp only [Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.one_im, h]
      field_simp
      ring
  inv_zero := by ext <;> simp
  nnqsmul := _
  qsmul := _

end LADRDW
