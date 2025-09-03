import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

namespace DyadicRat

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by
      intro x y z hxy hyz
      have h : x.numerator * z.denominator * y.denominator= z.numerator * x.denominator * y.denominator := by
        grind
      field_simp [y.nonzero] at h
      exact h
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

def PreRatZero : PreRat := ⟨ 0, 1, by decide ⟩

theorem PreRatZero.equiv (a : PreRat) : a ≈ PreRatZero ↔ a.numerator = 0 := by
  rw [PreRat.eq]
  simp [PreRatZero]

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ)  : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd, Setoid.r]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quot.ind _ n; intro ⟨ a, b, h ⟩
  use a, b; refine ⟨ h, ?_ ⟩
  simp [formalDiv, h]; rfl

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    grind
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp [Setoid.r, h1, h2, h1', h2'] at *
    calc
      _ = (a*b')*(c*d') := by ring
      _ = (a'*b)*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, h1 ⟩ ⟨ a', b', h2 ⟩ h3
    simp [Setoid.r, h1, h2] at *
    exact h3
  )

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, add_eq _ _ (by positivity) (by positivity), eq _ _ (by norm_num) (by norm_num)]
  omega

lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, mul_eq, eq]
  ring
  all_goals positivity

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a b h
  dsimp at h
  rw [coe_Int_eq, coe_Int_eq, eq] at h
  simp at h
  exact h
  all_goals positivity

lemma formalDiv_zero (a:ℤ) : a // 0 = 0 := by rfl

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
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
        by_contra h4
        have : a ≈ PreRatZero := Setoid.symm (Setoid.trans h4.symm h.symm)
        exact h2 this

      rw [PreRatZero.equiv] at h2 h3
      rw [eq _ _ h2 h3, mul_comm, ← h, mul_comm]
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
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
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf

  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by
  intro x
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff x
  rw [show (0:Rat) = 0 // 1 by rfl]
  rw [add_eq _ _ (by norm_num) hb]
  rw [eq _ _ (by simp [hb]) hb]
  simp
 ) (by
  intro a
  obtain ⟨ a, b, hb , rfl ⟩ := eq_diff a
  rw [neg_eq _ hb]
  rw [add_eq _ _ hb hb]
  rw [show (0:Rat) = 0 // 1 by rfl]
  rw [eq]
  ring
  positivity
  norm_num
 )
