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
theorem extractInverse_spec {R} [Ring R] (a : R) (h : MyIsUnit' a) : a * extractInverse a h = 1 ∧ extractInverse a h * a = 1 := Classical.choose_spec h
theorem extractInverse_spec' {R} [Ring R] (a : R) (h : MyIsUnit' a) : MyIsUnit' (extractInverse a h) := by
  use a
  simp [extractInverse_spec]

@[ext]
structure MyUnits' (R) [Ring R] where
  val : R
  prop : MyIsUnit' val

attribute [coe] MyUnits'.val

instance {R} [Ring R] : Coe (MyUnits' R) R where
  coe a := a.val

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
    val := extractInverse a.val a.prop,
    prop := extractInverse_spec' a.val a.prop
  }

lemma inv_val_eq {R} [Ring R] (a : MyUnits' R) : (a⁻¹).val = extractInverse a.val a.prop := rfl

lemma MyUnits'.inv_mul {R} [Ring R] (a : MyUnits' R)
: a⁻¹.val * a.val = 1 := by
  have := extractInverse_spec a.val a.prop
  rw [inv_val_eq]
  grind

lemma MyUnits'.mul_inv {R} [Ring R] (a : MyUnits' R)
: a.val * a⁻¹.val = 1 := by
  have := extractInverse_spec a.val a.prop
  rw [inv_val_eq]
  grind

instance MyUnits'.instMul {R} [Ring R] : Mul (MyUnits' R) where
  mul a b := {
    val := a * b,
    prop := by
      use b⁻¹ * a⁻¹
      constructor
      rw [show a * b * (b⁻¹ * a⁻¹) = a.val * (b * b⁻¹) * a⁻¹ by simp [mul_assoc]]
      rw [mul_inv, mul_one, mul_inv]

      rw [show b⁻¹.val * a⁻¹.val * (a.val * b.val) = b⁻¹.val * (a⁻¹.val * a.val) * b.val by simp [mul_assoc]]
      rw [inv_mul, mul_one, inv_mul]
  }

lemma MyUnits'.mul_val {R} [Ring R] (a b : MyUnits' R) : (a * b).val = a.val * b.val := rfl

instance MyUnits'.instOne {R} [Ring R] : One (MyUnits' R) where
  one := {
    val := 1,
    prop := by
      use 1
      simp
  }

lemma MyUnits'.one_val {R} [Ring R] : (1 : MyUnits' R).val = 1 := rfl

noncomputable instance MyUnits'.instGroup {R} [Ring R] : Group (MyUnits' R) where
  mul_assoc := by
    rintro a b c
    ext
    simp [mul_val, mul_assoc]
  one_mul := by
    rintro a
    ext
    simp [mul_val, one_val, one_mul]
  mul_one := by
    rintro a
    ext
    simp [mul_val, one_val, mul_one]
  inv_mul_cancel := by
    rintro a
    ext
    simp [mul_val, inv_mul, one_val]

/-
# Relation between units and zero divisors
-/
def IsZeroDivisor {R} [Ring R] (a : R) : Prop := a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ (a * b = 0 ∨ b * a = 0)

lemma Ring.not_isUnit_of_isZeroDivisor {R} [Ring R] (a : R) (h : IsZeroDivisor a) : ¬MyIsUnit' a := by
  by_contra h2
  unfold IsZeroDivisor at h
  obtain ⟨ a_ne_0, ⟨ b, b_ne_0, h | h ⟩ ⟩ := h

  -- In this branch, suppose ab = 0 for some nonzero b

  obtain ⟨ v, _, hv2 ⟩ := h2 -- Then, va = 1 for some v
  have := calc
    b = 1 * b := by simp
    _ = (v * a) * b := by simp [hv2]
    _ = v * (a * b) := by simp [mul_assoc]
    _ = v * 0 := by rw [h]
    _ = 0 := by simp [mul_zero]
  exact b_ne_0 this

  -- Similarly if ba = 0 for some nonzero b...
  obtain ⟨ v, hv1, _ ⟩ := h2
  have := calc
    b = b * 1 := by simp
    _ = b * (a * v) := by simp [hv1]
    _ = (b * a) * v := by simp [mul_assoc]
    _ = 0 * a := by simp [h]
    _ = 0 := by simp [zero_mul]
  exact b_ne_0 this

/-
Example 1: The ring ℤ has no zero divisors
-/
example : ¬∃ a : ℤ, IsZeroDivisor a := by
  by_contra h
  obtain ⟨ a, ⟨ h2, ⟨ b, hb1, hb2 ⟩ ⟩ ⟩ := h
  grind [Int.mul_ne_zero]

/-
Example 1, continued: and its only units in ℤ are ±1
-/
example (a : ℤ) : MyIsUnit' a ↔ a = 1 ∨ a = -1 := by
  constructor
  grind [MyIsUnit', Int.eq_one_or_neg_one_of_mul_eq_one]

  rintro (rfl | rfl)
  · use 1
    norm_num
  · use -1
    norm_num

#eval (8 : ZMod 12).inv
/-
Example 2
-/
example (n : ℕ) (u : ℕ) (h : Nat.Coprime u n) : MyIsUnit' (u : ZMod n) := by
  unfold MyIsUnit'
  -- use Nat.gcdA u n
  grind [ZMod.coe_mul_inv_eq_one]

/-
# Example 5: The quadratic field ℚ[√D]
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

example {R} [CommRing R]
: (∀ (a b : R), a * b = 0 → a = 0 ∨ b = 0) ↔
¬∃ (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by grind


def IsIntegralDomain (R : Type*) [CommRing R] : Prop :=
  (1 ≠ 0) ∧ ∀ (a b : R), a * b = 0 → a = 0 ∨ b = 0

/-
Example 2
-/
example {R} [Ring R] (a b c : R) (ha : ¬ IsZeroDivisor a) (h : a * b = a * c)
: a = 0 ∨ b = c := by
  have : a * (b - c) = 0 := by grind [mul_sub]
  grind [IsZeroDivisor]

/-
# Definition (page 228): subrings
-/

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

/-
Exercise 21

The `ext` attribute generates a lemma `PRSet.ext_iff` that can be used to rewrite `a = b` to `a.val = b.val`. Note that the `ext` tactic will apply this lemma and then rewrite `a.val = b.val` to `x ∈ a.val ↔ x ∈ b.val`, which is too much rewriting.
-/
@[ext]
structure PRSet (G : Type*) where
  val : Set G

def ssd {G : Type*} (a b : Set G) : Set G := (a ∪ b) \ (a ∩ b)

/-
We can use `tauto` to grind through the proof of associativity, or `grind`
A more conceputal proof is that `x ∈ ssd a b` iff `XOR [x ∈ a, x ∈ b]`, hence both sides reduce to `XOR [x ∈ ssd a, x ∈ ssd b, x ∈ ssd c]`
-/
lemma ssd_assoc {G : Type*} (a b c : Set G) : ssd (ssd a b) c = ssd a (ssd b c) := by
  ext x
  simp [ssd]
  tauto

instance PRSet.instAdd {G} : Add (PRSet G) where
  add a b := {
    val := ssd a.val b.val
  }

lemma PRSet.add_val {G} (a b : PRSet G)
: (a + b).val = ssd a.val b.val := rfl

instance PRSet.instZero {G} : Zero (PRSet G) where
  zero := {
    val := ∅
  }

lemma PRSet.zero_val {G} : (0 : PRSet G).val = ∅ := rfl

instance PRSet.instNeg {G} : Neg (PRSet G) where
  neg a := a

lemma PRSet.neg_val {G} (a : PRSet G) : (-a).val = a.val := rfl

instance PRSet.instAddCommGroup {G} : AddCommGroup (PRSet G) where
  add_assoc a b c := by
    rw [PRSet.ext_iff]
    simp [add_val, ssd_assoc]
  zero_add a := by
    rw [PRSet.ext_iff]
    simp [add_val, zero_val, ssd]
  add_zero a := by
    rw [PRSet.ext_iff]
    simp [add_val, zero_val, ssd]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by
    rw [PRSet.ext_iff]
    simp [add_val, neg_val, ssd, zero_val]
  add_comm a b := by
    rw [PRSet.ext_iff]
    simp [add_val, ssd]
    grind

instance PRSet.instMul {G} : Mul (PRSet G) where
  mul a b := {
    val := a.val ∩ b.val
  }

lemma PRSet.mul_val {G} (a b : PRSet G)
: (a * b).val = a.val ∩ b.val := rfl

instance PRSet.instOne {G} : One (PRSet G) where
  one := {
    val := ⊤
  }

lemma PRSet.one_val {G} : (1 : PRSet G).val = ⊤ := rfl


instance PRSet.instRing {G} : Monoid (PRSet G) where
  mul_assoc a b c := by
    rw [PRSet.ext_iff]
    simp [mul_val]
    grind
  one_mul a := by
    rw [PRSet.ext_iff]
    simp [mul_val, one_val]
  mul_one a := by
    ext
    simp [mul_val, one_val]
