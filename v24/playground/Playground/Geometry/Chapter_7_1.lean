import Mathlib

set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.cases false

/-
This file formalizes the definitions, theorems and examples from Chapter 7.1 of Dummit and Foote (page 226).

We work with the Mathlib typeclasses `NonUnitalRing` and `Ring`.
-/

#check NonUnitalRing
#check Ring


instance : NonUnitalRing ℤ where
  add := Int.add
  add_assoc := by grind
  zero := 0
  zero_add := by grind
  add_zero := by grind
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by grind
  add_comm := by grind
  left_distrib := by grind
  right_distrib := by grind
  zero_mul := by grind
  mul_zero := by grind

#synth Ring (ZMod 6)

/-
# Examples from Matt Macauley

R1 - ZMod 6
R2, R3, R4 hanve the same additive structure, but different multiplicative structures
-/
structure R2 : Type where
  elem : ZMod 6
deriving DecidableEq

instance R2.instAdd : Add R2 where add a b := { elem := a.elem + b.elem }
lemma R2.add_eq (a b : R2) : a + b = ⟨ a.elem + b.elem ⟩ := rfl

instance R2.instZero : Zero R2 where zero := ⟨0⟩
lemma R2.zero_eq : (0 : R2) = ⟨0⟩ := rfl

instance R2.instNeg : Neg R2 where neg a := ⟨-a.elem⟩
lemma R2.neg_eq (a : R2) : -a = ⟨-a.elem⟩ := rfl

instance R2.instAddCommGroup : AddCommGroup R2 where
  add_assoc a b c := by simp [add_eq]; grind
  zero := ⟨0⟩
  zero_add := by simp [zero_eq, add_eq]
  add_zero := by simp [zero_eq, add_eq]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by simp [neg_eq, add_eq, zero_eq]
  add_comm := by simp [add_eq, add_comm]

instance R2.instMul : Mul R2 where mul _ _ := ⟨ 0 ⟩
lemma R2.mul_eq (a b : R2) : a * b = ⟨ 0 ⟩ := rfl

instance R2.instNonUnitalRing : NonUnitalRing R2 where
  zero_mul := by simp [zero_eq, mul_eq]
  mul_zero := by simp [zero_eq, mul_eq]
  mul_assoc := by simp [mul_eq]
  left_distrib := by simp [mul_eq, zero_eq]
  right_distrib := by simp [mul_eq, zero_eq]

structure R3 : Type where
  elem : ZMod 6
deriving Fintype, DecidableEq

instance R3.instAdd : Add R3 where add a b := { elem := a.elem + b.elem }
lemma R3.add_eq (a b : R3) : a + b = ⟨ a.elem + b.elem ⟩ := rfl

instance R3.instZero : Zero R3 where zero := ⟨0⟩
lemma R3.zero_eq : (0 : R3) = ⟨0⟩ := rfl

instance R3.instNeg : Neg R3 where neg a := ⟨-a.elem⟩
lemma R3.neg_eq (a : R3) : -a = ⟨-a.elem⟩ := rfl

instance R3.instAddCommGroup : AddCommGroup R3 where
  add_assoc a b c := by simp [add_eq]; grind
  zero := ⟨0⟩
  zero_add := by simp [zero_eq, add_eq]
  add_zero := by simp [zero_eq, add_eq]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by simp [neg_eq, add_eq, zero_eq]
  add_comm := by simp [add_eq, add_comm]

instance R3.instMul : Mul R3 where mul a b := ⟨ 4*a.elem*b.elem ⟩
lemma R3.mul_eq (a b : R3) : a * b = ⟨ 4*a.elem*b.elem ⟩ := rfl

instance R3.instNonUnitalRing : NonUnitalRing R3 where
  zero_mul := by simp [zero_eq, mul_eq]
  mul_zero := by simp [zero_eq, mul_eq]
  mul_assoc := by decide
  left_distrib := by decide
  right_distrib := by decide


structure R4 : Type where
  elem : ZMod 6
deriving Fintype, DecidableEq

instance R4.instAdd : Add R4 where add a b := { elem := a.elem + b.elem }
lemma R4.add_eq (a b : R4) : a + b = ⟨ a.elem + b.elem ⟩ := rfl

instance R4.instZero : Zero R4 where zero := ⟨0⟩
lemma R4.zero_eq : (0 : R4) = ⟨0⟩ := rfl

instance R4.instNeg : Neg R4 where neg a := ⟨-a.elem⟩
lemma R4.neg_eq (a : R4) : -a = ⟨-a.elem⟩ := rfl

instance R4.instAddCommGroup : AddCommGroup R4 where
  add_assoc a b c := by simp [add_eq]; grind
  zero := ⟨0⟩
  zero_add := by simp [zero_eq, add_eq]
  add_zero := by simp [zero_eq, add_eq]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by simp [neg_eq, add_eq, zero_eq]
  add_comm := by simp [add_eq, add_comm]

instance R4.instMul : Mul R4 where mul a b := ⟨ 3*a.elem*b.elem ⟩
lemma R4.mul_eq (a b : R4) : a * b = ⟨ 3*a.elem*b.elem ⟩ := rfl

instance R4.instNonUnitalRing : NonUnitalRing R4 where
  zero_mul := by simp [zero_eq, mul_eq]
  mul_zero := by simp [zero_eq, mul_eq]
  mul_assoc := by decide
  left_distrib := by decide
  right_distrib := by decide

/-
# Units and zero divisors
-/

def MyIsUnit' {R} [Ring R] (a : R) : Prop := ∃ b : R, a * b = 1 ∧ b * a = 1

noncomputable def extractInverse {R} [Ring R] (a : R) (h : MyIsUnit' a) : R := Exists.choose h

structure MyUnits' (R) [Ring R] where
  val : R
  prop : MyIsUnit' val


/-
In fact, only one of `val_inv` and `inv_val` is necessary; the other can be derived from the other.
-/

def Ring.AreInverse {G} [Ring G] (a b : G) : Prop := a * b = 1 ∧ b * a = 1

lemma Ring.AreInverse.symm {G} [Ring G] (a b : G) : AreInverse a b ↔ AreInverse b a := by grind [Ring.AreInverse]

lemma Ring.AreInverse.right_unique {G} [Ring G] (a b c : G) (hb : AreInverse a b) (hc : AreInverse a c) : c = b := by
  calc
    c = c * 1 := by simp [mul_one]
    _ = c * (a * b) := by (congr 1; rw [hb.1])
    _ = (c * a) * b := by rw [mul_assoc]
    _ = 1 * b := by (congr 1; rw [hc.2])
    _ = b := by simp [one_mul]


noncomputable instance {R} [Ring R] : Inv (MyUnits' R) where
  inv a := {
    val := Classical.choose a.prop,
    prop := by
      have := Classical.choose_spec a.prop
      grind [MyIsUnit']
  }

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

def MyIsZeroDivisor {R} [Ring R] (a : R) : Prop := a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ (a * b = 0 ∨ b * a = 0)
def MyIsUnit {R} [Ring R] (a : R) : Prop := ∃ b : MyUnits R, b.val = a

lemma Ring.not_isUnit_of_isZeroDivisor {R} [Ring R] (a : R) (h : MyIsZeroDivisor a) : ¬MyIsUnit a := by
  by_contra h2
  unfold MyIsZeroDivisor at h
  obtain ⟨ h3, ⟨ b, hb1, h | h ⟩ ⟩ := h
  · obtain ⟨ a, rfl ⟩ := h2
    have := calc
      b = 1 * b := by simp
      _ = (a.inv * a.val) * b := by simp [a.inv_val]
      _ = a.inv * (a.val * b) := by simp [mul_assoc]
      _ = a.inv * 0 := by rw [h]
      _ = 0 := by simp [mul_zero]
    exact hb1 this
  · obtain ⟨ a, rfl ⟩ := h2
    have := calc
      b = b * 1 := by simp
      _ = b * (a.val * a.inv) := by simp [a.val_inv]
      _ = (b * a.val) * a.inv := by simp [mul_assoc]
      _ = 0 * a.inv := by rw [h]
      _ = 0 := by simp [zero_mul]
    exact hb1 this

lemma MyUnits.mul_eq {R} [Ring R] (a b : MyUnits R) : (a * b).val = a.val * b.val := rfl

example (a b : ℤ) (h1 : a ≠ 0) (h2 : b ≠ 0) : a * b ≠ 0 := by exact Int.mul_ne_zero h1 h2
/-
Example 1: The ring ℤ has no zero divisors
-/
example : ¬∃ a : ℤ, MyIsZeroDivisor a := by
  by_contra h
  obtain ⟨ a, ⟨ h2, ⟨ b, hb1, hb2 ⟩ ⟩ ⟩ := h
  grind [Int.mul_ne_zero]

/-
Example 1: The only units in ℤ are ±1
-/
example (a : ℤ) : MyIsUnit a ↔ a = 1 ∨ a = -1 := by
  sorry

/-
# The quadratic field ℚ[√D]
-/

def QAdjoinSqrt (D : ℕ) : Subring ℝ where
  carrier := { a + b*√D | (a : ℚ) (b : ℚ) }
  mul_mem' := by
    rintro a b ⟨ a, b, rfl ⟩ ⟨ c, d, rfl ⟩
    use a * c + b * d * D, a * d + b * c
    -- it should be possible to run `plausible` here
    simp only [mul_add, add_mul]
    push_cast
    simp only [add_assoc]
    congr 1
    simp only [add_mul]
    rw [mul_comm (d : ℝ) _]
    simp only [← mul_assoc]
    nth_rw 4 [mul_comm _ (d : ℝ )]
    nth_rw 4 [mul_assoc (b : ℝ)]
    rw [show (√D : ℝ) * (√D : ℝ) = D by simp]
    ring_nf
  add_mem' := by
    rintro a b ⟨ a, b, rfl ⟩ ⟨ c, d, rfl ⟩
    use a + c, b + d
    simp
    rw [add_mul]
    simp only [← add_assoc]
    congr 1
    nth_rw 2 [add_comm _ (c : ℝ)]
    simp only [← add_assoc]
    congr 1
    rw [add_comm]
  zero_mem' := by
    use 0, 0
    simp
  neg_mem' := by
    intro x hx
    obtain ⟨ a, b, rfl ⟩ := hx
    use -a, -b
    -- there should be a tactic for this
    rw [neg_add]
    congr
    norm_num
    rw [← neg_mul]
    congr
    norm_num
  one_mem' := by
    use 1, 0
    simp

def ZAdjoinSqrt (D : ℕ) : Subring ℝ where
  carrier := { a + b*√D | (a : ℤ) (b : ℤ) }
  mul_mem' := by
    rintro a b ⟨ a, b, rfl ⟩ ⟨ c, d, rfl ⟩
    use a * c + b * d * D, a * d + b * c
    -- it should be possible to run `plausible` here
    simp only [mul_add, add_mul]
    push_cast
    simp only [add_assoc]
    congr 1
    simp only [add_mul]
    rw [mul_comm (d : ℝ) _]
    simp only [← mul_assoc]
    nth_rw 4 [mul_comm _ (d : ℝ )]
    nth_rw 4 [mul_assoc (b : ℝ)]
    rw [show (√D : ℝ) * (√D : ℝ) = D by simp]
    ring_nf
  add_mem' := by
    rintro a b ⟨ a, b, rfl ⟩ ⟨ c, d, rfl ⟩
    use a + c, b + d
    simp
    rw [add_mul]
    simp only [← add_assoc]
    congr 1
    nth_rw 2 [add_comm _ (c : ℝ)]
    simp only [← add_assoc]
    congr 1
    rw [add_comm]
  zero_mem' := by
    use 0, 0
    simp
  neg_mem' := by
    intro x hx
    obtain ⟨ a, b, rfl ⟩ := hx
    use -a, -b
    -- there should be a tactic for this
    rw [neg_add]
    congr
    norm_num
    rw [← neg_mul]
    congr
    norm_num
  one_mem' := by
    use 1, 0
    simp

noncomputable def smallUnit : QAdjoinSqrt 2 := ⟨1 + √2, by use 1, 1; norm_num⟩
noncomputable def smallUnitInv : QAdjoinSqrt 2 := ⟨-1 + √2, by
  use -1, 1
  norm_num
⟩
noncomputable def smallUnitConjugate : QAdjoinSqrt 2 := ⟨1 - √2, by
  use 1, -1
  norm_num
  congr
⟩

noncomputable def smallUnit' : Units (QAdjoinSqrt 2) := ⟨smallUnit, smallUnitInv, by
  simp only [smallUnit, smallUnitInv]
  apply Subtype.eq
  simp [add_mul, mul_add]
  ring
, by
  simp only [smallUnit, smallUnitInv]
  apply Subtype.eq
  simp [add_mul, mul_add]
  ring
⟩


#check Zsqrtd 5


#check Units (QAdjoinSqrt 5)

-- Can I use QuadraticAlgebra to do this?
#check QuadraticAlgebra

abbrev F := QuadraticAlgebra ℚ 5 0

def x : F := ⟨1/2, ⟩

#eval x

/-
Example : ℤ is a subring of ℚ and ℚ is a subring of ℝ
-/

def IntSubring : Subring ℝ where
  carrier := { a | a : ℤ }
  mul_mem' := by
    rintro a b ⟨ a, rfl ⟩ ⟨ b, rfl ⟩
    use a * b
    norm_cast
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ a, rfl ⟩ ⟨ b, rfl ⟩
    use a + b
    norm_cast
  neg_mem' := by
    rintro a ⟨ a, rfl ⟩
    use -a
    norm_cast
  one_mem' := by
    use 1
    norm_cast

def RatSubring : Subring ℝ where
  carrier := { a | a : ℚ }
  mul_mem' := by
    rintro a b ⟨ a, rfl ⟩ ⟨ b, rfl ⟩
    use a * b
    norm_cast
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ a, rfl ⟩ ⟨ b, rfl ⟩
    use a + b
    norm_cast
  neg_mem' := by
    rintro a ⟨ a, rfl ⟩
    use -a
    norm_cast
  one_mem' := by
    use 1
    norm_cast

example : IntSubring ≤ RatSubring := by
  intro a ha
  obtain ⟨ a, rfl ⟩ := ha
  use a
  norm_cast

/-
Example : The even integers are a nonunital subring of ℤ
-/

example : NonUnitalSubring ℤ where
  carrier := { 2*a | a : ℤ }
  mul_mem' := by
    rintro a b ⟨ a, rfl ⟩ ⟨ b, rfl ⟩
    use 2 * a * b
    grind
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ a, rfl ⟩ ⟨ b, rfl ⟩
    use a + b
    grind
  neg_mem' := by
    rintro a ⟨ a, rfl ⟩
    use -a
    grind

/-
The ring of continuous functions on the real line is a subring of the ring of all functions on the real line, and contains the differentiable functions as a subring.
-/



/-
Exercise 1
-/
example {G} [Ring G] : (-1 : G)^2 = 1 := by
  have : ((-1 : G) + (1 : G))^2 = 0 := by
    rw [neg_add_cancel, sq, zero_mul]
  simp only [sq, left_distrib, right_distrib, one_mul, mul_one] at this
  rw [neg_add_cancel, add_zero] at this
  have := congr($this + 1)
  rw [zero_add] at this
  rw [add_assoc, neg_add_cancel, add_zero] at this
  rw [sq]
  exact this

#check Subring
