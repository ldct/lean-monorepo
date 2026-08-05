import Playground.Artin.Chapter_2_2

namespace Artin

class Monoid (M : Type*) extends Mul M, One M where
  mul_assoc : ∀ a b c : M, (a * b) * c = a * (b * c)
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

attribute [simp] Monoid.one_mul Monoid.mul_one

/- Exercise 2.2.2 -/

/- The type of bundled units of a monoid. -/
@[ext]
structure Units (M : Type*) [Monoid M] : Type _ where
  val : M
  inv : M
  inv_val : inv * val = 1
  val_inv : val * inv = 1

attribute [simp] Units.inv_val Units.val_inv

instance {M : Type*} [Monoid M] : Mul (Units M) where
  mul a b := {
    val := a.val * b.val,
    inv := b.inv * a.inv,
    inv_val := by
      rw [← Monoid.mul_assoc, Monoid.mul_assoc b.inv]
      simp
    val_inv := by
      rw [← Monoid.mul_assoc, Monoid.mul_assoc a.val]
      simp
  }
@[simp] lemma Units.mul_val {M : Type*} [Monoid M] (a b : Units M) : (a * b).val = a.val * b.val := rfl
@[simp] lemma Units.mul_inv {M : Type*} [Monoid M] (a b : Units M) : (a * b).inv = b.inv * a.inv := rfl
instance {M : Type*} [Monoid M] : One (Units M) where
  one := {
    val := 1,
    inv := 1,
    inv_val := by simp,
    val_inv := by simp
  }
@[simp] lemma Units.one_val {M : Type*} [Monoid M] : (1 : Units M).val = 1 := rfl
@[simp] lemma Units.one_inv {M : Type*} [Monoid M] : (1 : Units M).inv = 1 := rfl

instance {M : Type*} [Monoid M] : Inv (Units M) where
  inv a := {
    val := a.inv,
    inv := a.val,
    inv_val := by simp,
    val_inv := by simp
  }
@[simp] lemma Units.inv_inv {M : Type*} [Monoid M] (a : Units M) : (a⁻¹).inv = a.val := rfl
@[simp] lemma Units.inv_val' {M : Type*} [Monoid M] (a : Units M) : (a⁻¹).val = a.inv := rfl

example {M : Type*} [Monoid M] : Group (Units M) where
  mul_assoc := by
    rintro ⟨a, a_inv⟩ ⟨b, b_inv⟩ ⟨c, c_inv⟩
    ext
    <;> simp [Monoid.mul_assoc]
  one_mul := by
    rintro ⟨a, a_inv⟩
    ext <;> simp
  mul_one := by
    rintro ⟨a, a_inv⟩
    ext <;> simp
  inv_mul_cancel := by
    rintro ⟨a, a_inv⟩
    ext <;> simp_all
  mul_inv_cancel := by
    rintro ⟨a, a_inv⟩
    ext <;> simp_all

-- 2.4.b

def IsSubgroup {G : Type*} [Group G] (C : Set G) : Prop :=
  ∃ H : Subgroup G, H.carrier = C

def TwoElementSubgroupOfR : Subgroup NonZeroReal where
  carrier := { x | x = ⟨1, by simp⟩ ∨ x = ⟨-1, by simp⟩ }
  one_mem := by
    simp only [Set.mem_setOf_eq]
    left
    ext
    grind [NonZeroReal.val_one]
  mul_mem := by
    rintro x y (rfl | rfl) (rfl | rfl)
    · left
      ext
      simp [NonZeroReal.val_mul]
    · right
      ext
      simp [NonZeroReal.val_mul]
    · right
      ext
      simp [NonZeroReal.val_mul]
    · left
      ext
      simp [NonZeroReal.val_mul]
  inv_mem := by
    rintro x (rfl | rfl)
    · left
      ext
      simp [NonZeroReal.val_inv]
    · right
      ext
      simp [NonZeroReal.val_inv]

example : IsSubgroup { x : NonZeroReal | x = ⟨1, by simp⟩ ∨ x = ⟨-1, by simp⟩ } := by
  use TwoElementSubgroupOfR
  simp [TwoElementSubgroupOfR]

/- Exercise 2.2.6 -/

@[ext]
structure Opposite (G : Type*) [Group G] : Type _ where
  val : G

instance {G : Type*} [Group G] : One (Opposite G) where
  one := {
    val := 1,
  }
@[simp] lemma one_val {G : Type*} [Group G] : (1 : Opposite G).val = 1 := rfl

instance {G : Type*} [Group G] : Inv (Opposite G) where
  inv a := {
    val := a.val⁻¹,
  }
lemma inv_val {G : Type*} [Group G] (a : Opposite G) : (a⁻¹).val = a.val⁻¹ := rfl

instance {G : Type*} [Group G] : Mul (Opposite G) where
  mul a b := {
    val := b.val * a.val,
  }
lemma mul_val {G : Type*} [Group G] (a b : Opposite G) : (a * b).val = b.val * a.val := rfl

instance {G : Type*} [Group G] : Group (Opposite G) where
  mul_assoc := by
    rintro a b c
    ext
    simp [mul_val, Group.mul_assoc]
  one_mul := by
    rintro a
    ext
    simp [mul_val]
  mul_one := by
    rintro a
    ext
    simp [mul_val]
  inv_mul_cancel := by
    rintro a
    ext
    simp [mul_val, inv_val]
  mul_inv_cancel := by
    rintro a
    ext
    simp [mul_val, inv_val]

end Artin
