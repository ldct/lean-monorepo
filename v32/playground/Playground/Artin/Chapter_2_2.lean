import Mathlib

/-
https://web.ma.utexas.edu/users/vandyke/notes/250a_notes/main.pdf
-/

variable {α : Type*}

namespace Artin

class Group (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

attribute [simp] Group.one_mul Group.mul_one Group.inv_mul_cancel Group.mul_inv_cancel

/- Example 2.2.2 -/
@[ext]
public structure NonZeroReal : Type where
  val : ℝ
  ne_zero : val ≠ 0
instance : Mul NonZeroReal where mul := fun a b => ⟨a.val * b.val, by simp [NonZeroReal.ne_zero]⟩
lemma NonZeroReal.val_mul (a b : NonZeroReal) : (a * b).val = a.val * b.val := rfl
instance : One NonZeroReal where one := ⟨1, by simp⟩
lemma NonZeroReal.val_one : (1 : NonZeroReal).val = 1 := rfl
noncomputable instance : Inv NonZeroReal where
  inv := fun a => ⟨a.val⁻¹, by simp [NonZeroReal.ne_zero]⟩
lemma NonZeroReal.val_inv (a : NonZeroReal) : (a⁻¹).val = a.val⁻¹ := rfl
noncomputable instance NonZeroReal.Group : Group NonZeroReal where
  mul_assoc := by
    rintro ⟨a, h⟩ ⟨b, hb⟩ ⟨c, hc⟩
    ext
    grind [val_mul, val_mul, val_mul]
  one_mul := by
    rintro ⟨a, h⟩
    ext
    grind [val_mul, val_one]
  mul_one := by
    rintro ⟨a, h⟩
    ext
    grind [val_mul, val_one]
  inv_mul_cancel := by
    rintro ⟨a, h⟩
    ext
    grind [val_mul, val_inv, val_one]
  mul_inv_cancel := by
    rintro ⟨a, h⟩
    ext
    grind [val_mul, val_inv, val_one]

@[ext]
structure NonZeroComplex : Type where
  val : ℂ
  ne_zero : val ≠ 0
instance : Mul NonZeroComplex where mul := fun a b => ⟨a.val * b.val, by simp [NonZeroComplex.ne_zero]⟩
@[simp] lemma NonZeroComplex.val_mul (a b : NonZeroComplex) : (a * b).val = a.val * b.val := rfl
instance : One NonZeroComplex where one := ⟨1, by simp⟩
@[simp] lemma NonZeroComplex.val_one : (1 : NonZeroComplex).val = 1 := rfl
noncomputable instance : Inv NonZeroComplex where
  inv := fun a => ⟨a.val⁻¹, by simp [NonZeroComplex.ne_zero]⟩
@[simp] lemma NonZeroComplex.val_inv (a : NonZeroComplex) : (a⁻¹).val = a.val⁻¹ := rfl
noncomputable instance NonZeroComplex.Group : Group NonZeroComplex where
  mul_assoc := by
    rintro ⟨a, h⟩ ⟨b, hb⟩ ⟨c, hc⟩
    ext ; simp ; grind
  one_mul := by
    rintro ⟨a, h⟩
    ext ; simp
  mul_one := by
    rintro ⟨a, h⟩
    ext ; simp
  inv_mul_cancel := by
    rintro ⟨a, h⟩
    ext ; simp ; grind
  mul_inv_cancel := by
    rintro ⟨a, h⟩
    ext ; simp ; grind


/- Proposition 2.2.3 -/
lemma Group.left_cancel {G} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  have := congr(a⁻¹ * $h)
  rw [← mul_assoc, ← mul_assoc] at this
  simp_all

/- Proposition 2.2.3 -/
lemma Group.right_cancel {G} [Group G] (a b c : G) (h : b * a = c * a) : b = c := by
  have := congr($h * a⁻¹)
  rw [mul_assoc, mul_assoc] at this
  simp_all

/- Example 2.2.4 -/
instance (n : ℕ) : Group (GL (Fin n) ℝ) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel
  mul_inv_cancel := mul_inv_cancel

abbrev S (n : ℕ) := Equiv (Fin n) (Fin n)

instance (n : ℕ) : Group (S n) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel
  mul_inv_cancel := mul_inv_cancel


open Nat in
lemma S.size (n : ℕ) : (Fintype.card (S n)) = n ! := by
  rw [Fintype.card_perm]
  simp

@[ext]
structure S3 : Type where
  val : S 3
deriving DecidableEq

namespace S3

instance : Mul S3 where mul a b := ⟨a.val * b.val⟩
instance : One S3 where one := ⟨1⟩
instance : Inv S3 where inv a := ⟨a.val⁻¹⟩
instance : HPow S3 ℕ S3 where hPow a n := ⟨a.val ^ n⟩
instance : HPow S3 ℤ S3 where hPow a n := ⟨a.val ^ n⟩

@[simp] lemma val_mul (a b : S3) : (a * b).val = a.val * b.val := rfl
@[simp] lemma val_one : (1 : S3).val = 1 := rfl
@[simp] lemma val_inv (a : S3) : (a⁻¹).val = a.val⁻¹ := rfl

instance : Group S3 where
  mul_assoc a b c := by ext1; simp [mul_assoc]
  one_mul a := by ext1; simp
  mul_one a := by ext1; simp
  inv_mul_cancel a := by ext1; simp
  mul_inv_cancel a := by ext1; simp

def x : S3 := ⟨c[0, 1, 2]⟩
def y : S3 := ⟨Equiv.swap 0 1⟩

unsafe instance : Repr S3 := ⟨fun w p => reprPrec w.val p⟩

#eval y
#eval y * y = 1

/- Example 2.2.7 -/
#eval List.Pairwise (· ≠ ·) [1, x, x^2, y, x*y, x^2*y]

/- Example 2.2.8 -/
#eval x⁻¹ * y^3 * x^2 * y

-- TODO write this proof with rewrite rules

-- S3 is not abelian

#eval x * y = y * x

end S3

/- Definition 2.2.9 -/
@[ext] structure Subgroup (G : Type*) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ x y : G, x ∈ carrier → y ∈ carrier → x * y ∈ carrier
  inv_mem : ∀ x : G, x ∈ carrier → x⁻¹ ∈ carrier

instance {G : Type*} [Group G] : CoeSort (Subgroup G) (Type _) where
  coe H := { x : G // x ∈ H.carrier }

/- Example 2.2.10.a, the subgroup of complex numbers with modulus 1 -/
def NonZeroComplex.circleGroup : Subgroup NonZeroComplex where
  carrier := { z : NonZeroComplex | norm z.val = 1 }
  one_mem := by simp [val_one]
  mul_mem := by
    rintro ⟨a, h⟩ ⟨b, hb⟩ ha hb
    simp [val_mul] at *
    grind
  inv_mem := by
    rintro ⟨a, h⟩ ha
    simp_all

/- Example 2.2.11, the special linear group -/
def SpecialLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℝ) where
  carrier := { A : GL (Fin n) ℝ | A.det = 1 }
  one_mem := by grind
  mul_mem := by grind
  inv_mem := by simp

end Artin
