import Mathlib



namespace Chapter_7_1_appendix

def Ring.AreInverse {G} [Ring G] (a b : G) : Prop := a * b = 1 ∧ b * a = 1

lemma Ring.AreInverse.symm {G} [Ring G] (a b : G) : AreInverse a b ↔ AreInverse b a := by grind [Ring.AreInverse]

lemma Ring.AreInverse.right_unique {G} [Ring G] (a b c : G) (hb : AreInverse a b) (hc : AreInverse a c) : c = b := by
  calc
    c = c * 1 := by simp [mul_one]
    _ = c * (a * b) := by (congr 1; rw [hb.1])
    _ = (c * a) * b := by rw [mul_assoc]
    _ = 1 * b := by (congr 1; rw [hc.2])
    _ = b := by simp [one_mul]

/-
# A computable version of units where we store the inverse in the structure
-/
@[ext]
structure MyUnits (R) [Ring R] where
  val : R
  inv : R
  val_inv : val * inv = 1
  inv_val : inv * val = 1

lemma MyUnits.eq_of_val_eq {R} [Ring R] (a b : MyUnits R) (h : a.val = b.val) : a = b := by
  ext
  · exact h
  have h1 : Ring.AreInverse a.val a.inv := by simp [Ring.AreInverse, a.val_inv, a.inv_val]
  have h2 : Ring.AreInverse a.val b.inv := by simp [h, Ring.AreInverse, b.val_inv, b.inv_val]
  have h3 := Ring.AreInverse.right_unique _ _ _ h1 h2
  simp [h3]

instance MyUnits.instInv {R} [Ring R] : Inv (MyUnits R) where
  inv a := {
    val := a.inv,
    inv := a.val,
    val_inv := by simp [a.inv_val],
    inv_val := by simp [a.val_inv]
  }

lemma MyUnits.inv_val_eq_inv {R} [Ring R] (a : MyUnits R) : (a⁻¹).val = a.inv := rfl

instance MyUnits.instMul {R} [Ring R] : Mul (MyUnits R) where
  mul a b := {
    val := a.val * b.val,
    inv := b.inv * a.inv,
    val_inv := by
      rw [show a.val * b.val * (b.inv * a.inv) = a.val * (b.val * b.inv) * a.inv by simp [mul_assoc]]
      simp [a.val_inv, b.val_inv]
    inv_val := by
      rw [show b.inv * a.inv * (a.val * b.val) = b.inv * (a.inv * a.val) * b.val by simp [mul_assoc]]
      simp [b.inv_val, a.inv_val]
  }

lemma MyUnits.mul_val {R} [Ring R] (a b : MyUnits R) : (a * b).val = a.val * b.val := rfl

instance MyUnits.instOne {R} [inst : Ring R] : One (MyUnits R) where
  one := {
    val := 1,
    inv := 1,
    val_inv := by simp [inst.mul_one],
    inv_val := by simp [inst.mul_one]
  }

lemma MyUnits.one_val {R} [Ring R] : (1 : MyUnits R).val = 1 := rfl

instance MyUnits.instGroup {R} [inst : Ring R] : Group (MyUnits R) where
  mul_assoc a b c := by
    apply eq_of_val_eq
    simp [mul_val, mul_assoc]
  one_mul a := by
    apply eq_of_val_eq
    simp only [mul_val, one_val, one_mul]
  mul_one a := by
    apply eq_of_val_eq
    simp only [mul_val, one_val, mul_one]
  inv_mul_cancel a := by
    apply eq_of_val_eq
    simp only [mul_val, inv_val_eq_inv, a.inv_val, one_val]

def MyIsUnit {R} [Ring R] (a : R) : Prop := ∃ b : MyUnits R, b.val = a


def MyIsZeroDivisor {R} [Ring R] (a : R) : Prop := a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ (a * b = 0 ∨ b * a = 0)

lemma Ring.not_isUnit_of_isZeroDivisor {R} [Ring R] (a : R) (h : MyIsZeroDivisor a) : ¬MyIsUnit a := by
  by_contra h2
  unfold MyIsZeroDivisor at h
  obtain ⟨ _, ⟨ b, b_ne_0, h | h ⟩ ⟩ := h
  · obtain ⟨ a, rfl ⟩ := h2
    have := calc
      b = 1 * b := by simp
      _ = (a.inv * a.val) * b := by simp [a.inv_val]
      _ = a.inv * (a.val * b) := by simp [mul_assoc]
      _ = a.inv * 0 := by rw [h]
      _ = 0 := by simp [mul_zero]
    exact b_ne_0 this
  · obtain ⟨ a, rfl ⟩ := h2
    have := calc
      b = b * 1 := by simp
      _ = b * (a.val * a.inv) := by simp [a.val_inv]
      _ = (b * a.val) * a.inv := by simp [mul_assoc]
      _ = 0 * a.inv := by rw [h]
      _ = 0 := by simp [zero_mul]
    exact hb1 this


end Chapter_7_1_appendix