import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-
Construction of rational numbers as a quotient type
-/

set_option linter.style.emptyLine false

namespace Rational

attribute [grind <=] mul_right_cancel₀
attribute [grind .] Int.mul_ne_zero

structure PreRat where
  num : ℤ
  den : ℤ
  nz : den ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.num * b.den = b.num * a.den
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by
      intro x y z hxy hyz
      have h : x.num * z.den * y.den = z.num * x.den * y.den := by
        grind
      grind [y.nz]
    }

theorem PreRat.eq (a b c d : ℤ) (hb : b ≠ 0) (hd : d ≠ 0)
: (⟨ a,b,hb ⟩ : PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

@[grind =]
theorem PreRat.eq' (x y : PreRat) : x ≈ y ↔ x.num * y.den = x.den * y.num := by
  rw [PreRat.eq]
  grind

@[grind]
def PreRatZero : PreRat := ⟨ 0, 1, by decide ⟩

theorem PreRatZero.equiv (a : PreRat) : a ≈ PreRatZero ↔ a.num = 0 := by
  grind

def Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
def Rat.formalDiv (a b : ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

lemma Rat.formalDiv_eq (a b : ℤ) : formalDiv a b = Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩) := rfl

lemma Rat.formalDiv_eq' (a b : ℤ) (hb : b ≠ 0) : formalDiv a b = Quotient.mk PreRat.instSetoid  ⟨ a,b,hb ⟩ := by
  simp only [formalDiv_eq]
  rw [Quotient.eq]
  simp only [Setoid.r]
  grind

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
@[grind =]
theorem Rat.eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) : a // b = c // d ↔ a * d = c * b := by
  repeat rw [formalDiv_eq' _ _ (by positivity)]
  rw [Quotient.eq]
  simp only [Setoid.r]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n : Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quot.ind _ n
  intro ⟨ a, b, h ⟩
  use a, b; refine ⟨ h, ?_ ⟩
  simp [formalDiv, h]
  rfl

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (
    fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)
  ) (by
    intro ⟨ a, b, _ ⟩ ⟨ c, d, _ ⟩ ⟨ a', b', _ ⟩ ⟨ c', d', _ ⟩
    grind [formalDiv_eq']
  )

/-- Definition 4.2.2 (Addition of rationals) -/
@[grind =]
theorem Rat.add_eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, _ ⟩ ⟨ c, d, _ ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, _ ⟩ ⟨ c, d, _ ⟩ ⟨ a', b', _ ⟩ ⟨ c', d', _ ⟩
    grind [formalDiv_eq, Quotient.sound]
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, _ ⟩ ⟨ a', b', _ ⟩
    grind [formalDiv_eq']
  )

/-- Definition 4.2.2 (Negation of rationals) -/
@[grind =]
theorem Rat.neg_eq (a : ℤ) {b : ℤ} (hb : b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n : ℤ) // 1

instance Rat.instOfNat {n : ℕ} : OfNat Rat n where
  ofNat := (n : ℤ) // 1

@[grind =]
lemma Rat.zero_eq : (0 : Rat) = 0 // 1 := by rfl

@[grind =]
theorem Rat.coe_Int_eq (a : ℤ) : (a : Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n : ℕ) : (n : Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n : ℕ) : (ofNat(n) : Rat) = (ofNat(n) : Nat) // 1 := rfl

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b : ℤ) : (a : Rat) + (b : Rat) = (a+b : ℤ) := by
  grind

lemma Rat.intCast_mul (a b : ℤ) : (a : Rat) * (b : Rat) = (a*b : ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, mul_eq, eq]
  · ring
  all_goals positivity

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a : ℤ) : - (a : Rat) = (-a : ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n : ℤ ↦ (n : Rat)) := by
  intro a b h
  grind


lemma formalDiv_zero (a : ℤ) : a // 0 = 0 := by rfl

/-- Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro a b h
    obtain h1 | h2 := Classical.em (a ≈ PreRatZero)
    · have h3 : (b ≈ PreRatZero) := Setoid.trans (Setoid.symm h) h1
      rw [PreRatZero.equiv] at h1 h3
      simp_all [formalDiv_zero]
    · have h3 : ¬(b ≈ PreRatZero) := by
        grind [Setoid.symm, Setoid.trans]
      grind [PreRatZero.equiv]
)

lemma Rat.inv_eq (a : ℤ) {b : ℤ} (hb : b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd , rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf , rfl ⟩ := eq_diff z
  grind
)
 (by
  intro x
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff x
  grind
 ) (by
  intro a
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff a
  grind
 )

instance : CommRing Rat where
  add_comm := by
    intro x y
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    obtain ⟨c, d, hd, rfl⟩ := Rat.eq_diff y
    grind
  add_assoc := by
    intro x y z
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    obtain ⟨c, d, hd, rfl⟩ := Rat.eq_diff y
    obtain ⟨e, f, hf, rfl⟩ := Rat.eq_diff z
    grind
  add_zero := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    grind
  zero_add := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    grind
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    grind
  mul_comm := by
    intro x y
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    obtain ⟨c, d, hd, rfl⟩ := Rat.eq_diff y
    rw [Rat.mul_eq _ _ hb hd, Rat.mul_eq _ _ hd hb,
        Rat.eq _ _ (mul_ne_zero hb hd) (mul_ne_zero hd hb)]
    ring
  mul_assoc := by
    intro x y z
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    obtain ⟨c, d, hd, rfl⟩ := Rat.eq_diff y
    obtain ⟨e, f, hf, rfl⟩ := Rat.eq_diff z
    rw [Rat.mul_eq _ _ hb hd, Rat.mul_eq _ _ hd hf,
        Rat.mul_eq _ _ (mul_ne_zero hb hd) hf, Rat.mul_eq _ _ hb (mul_ne_zero hd hf),
        Rat.eq _ _ (mul_ne_zero (mul_ne_zero hb hd) hf) (mul_ne_zero hb (mul_ne_zero hd hf))]
    ring
  one_mul := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    rw [Rat.of_Nat_eq, Rat.mul_eq _ _ one_ne_zero hb,
        Rat.eq _ _ (mul_ne_zero one_ne_zero hb) hb]
    ring
  mul_one := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    rw [Rat.of_Nat_eq, Rat.mul_eq _ _ hb one_ne_zero,
        Rat.eq _ _ (mul_ne_zero hb one_ne_zero) hb]
    ring
  left_distrib := by
    intro x y z
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    obtain ⟨c, d, hd, rfl⟩ := Rat.eq_diff y
    obtain ⟨e, f, hf, rfl⟩ := Rat.eq_diff z
    rw [Rat.add_eq _ _ hd hf, Rat.mul_eq _ _ hb (mul_ne_zero hd hf),
        Rat.mul_eq _ _ hb hd, Rat.mul_eq _ _ hb hf,
        Rat.add_eq _ _ (mul_ne_zero hb hd) (mul_ne_zero hb hf),
        Rat.eq _ _ (mul_ne_zero hb (mul_ne_zero hd hf))
                    (mul_ne_zero (mul_ne_zero hb hd) (mul_ne_zero hb hf))]
    ring
  right_distrib := by
    intro x y z
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    obtain ⟨c, d, hd, rfl⟩ := Rat.eq_diff y
    obtain ⟨e, f, hf, rfl⟩ := Rat.eq_diff z
    rw [Rat.add_eq _ _ hb hd, Rat.mul_eq _ _ (mul_ne_zero hb hd) hf,
        Rat.mul_eq _ _ hb hf, Rat.mul_eq _ _ hd hf,
        Rat.add_eq _ _ (mul_ne_zero hb hf) (mul_ne_zero hd hf),
        Rat.eq _ _ (mul_ne_zero (mul_ne_zero hb hd) hf)
                    (mul_ne_zero (mul_ne_zero hb hf) (mul_ne_zero hd hf))]
    ring
  zero_mul := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    rw [Rat.zero_eq, Rat.mul_eq _ _ one_ne_zero hb,
        Rat.eq _ _ (mul_ne_zero one_ne_zero hb) one_ne_zero]
    ring
  mul_zero := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
    rw [Rat.zero_eq, Rat.mul_eq _ _ hb one_ne_zero,
        Rat.eq _ _ (mul_ne_zero hb one_ne_zero) one_ne_zero]
    ring
  natCast_succ := by
    intro n
    change (((n + 1) : ℤ) // 1 : Rat) = ((n : ℤ) // 1) + (1 : ℤ) // 1
    rw [Rat.add_eq _ _ one_ne_zero one_ne_zero,
        Rat.eq _ _ one_ne_zero (mul_ne_zero one_ne_zero one_ne_zero)]
    grind

end Rational
