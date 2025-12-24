import Mathlib

inductive MyQuaternionGroup (n : ℕ) : Type
  | a : ZMod (2 * n) → MyQuaternionGroup n
  | xa : ZMod (2 * n) → MyQuaternionGroup n
  deriving DecidableEq, Repr

namespace MyQuaternionGroup

variable {n : ℕ}

/-- Multiplication of the dihedral group.
-/
private def mul : MyQuaternionGroup n → MyQuaternionGroup n → MyQuaternionGroup n
  | a i, a j => a (i + j)
  | a i, xa j => xa (j - i)
  | xa i, a j => xa (i + j)
  | xa i, xa j => a (n + j - i)

/-- The identity `1` is given by `aⁱ`.
-/
private def one : MyQuaternionGroup n :=
  a 0

instance : Inhabited (MyQuaternionGroup n) :=
  ⟨one⟩

/-- The inverse of an element of the quaternion group.
-/
private def inv : MyQuaternionGroup n → MyQuaternionGroup n
  | a i => a (-i)
  | xa i => xa (n + i)

/-- The group structure on `MyQuaternionGroup n`.
-/
instance : Group (MyQuaternionGroup n) where
  mul := mul
  mul_assoc := by
    rintro (i | i) (j | j) (k | k) <;> simp only [(· * ·), mul] <;> ring_nf
    congr
    calc
      -(n : ZMod (2 * n)) = 0 - n := by rw [zero_sub]
      _ = 2 * n - n := by norm_cast; simp
      _ = n := by ring
  one := one
  one_mul := by
    rintro (i | i)
    · exact congr_arg a (zero_add i)
    · exact congr_arg xa (sub_zero i)
  mul_one := by
    rintro (i | i)
    · exact congr_arg a (add_zero i)
    · exact congr_arg xa (add_zero i)
  inv := inv
  inv_mul_cancel := by
    rintro (i | i)
    · exact congr_arg a (neg_add_cancel i)
    · exact congr_arg a (sub_self (n + i))

@[simp]
theorem a_mul_a (i j : ZMod (2 * n)) : a i * a j = a (i + j) :=
  rfl

@[simp]
theorem a_mul_xa (i j : ZMod (2 * n)) : a i * xa j = xa (j - i) :=
  rfl

@[simp]
theorem xa_mul_a (i j : ZMod (2 * n)) : xa i * a j = xa (i + j) :=
  rfl

@[simp]
theorem xa_mul_xa (i j : ZMod (2 * n)) : xa i * xa j = a ((n : ZMod (2 * n)) + j - i) :=
  rfl

@[simp]
theorem a_zero : a 0 = (1 : MyQuaternionGroup n) := by
  rfl

theorem one_def : (1 : MyQuaternionGroup n) = a 0 :=
  rfl

private def fintypeHelper : ZMod (2 * n) ⊕ ZMod (2 * n) ≃ MyQuaternionGroup n where
  invFun i :=
    match i with
    | a j => Sum.inl j
    | xa j => Sum.inr j
  toFun i :=
    match i with
    | Sum.inl j => a j
    | Sum.inr j => xa j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- If `0 < n`, then `MyQuaternionGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (MyQuaternionGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

deriving instance Repr for QuaternionGroup

def c' : Finset (QuaternionGroup 4) := { g | g ∈ (Subgroup.center (QuaternionGroup 4))}

#eval c'


instance : Nontrivial (MyQuaternionGroup n) :=
  ⟨⟨a 0, xa 0, by simp [- a_zero]⟩⟩

theorem card [NeZero n] : Fintype.card (MyQuaternionGroup n) = 4 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]
  ring

@[simp]
theorem a_one_pow (k : ℕ) : (a 1 : MyQuaternionGroup n) ^ k = a k := by
  induction k with
  | zero => rw [Nat.cast_zero]; rfl
  | succ k IH =>
    rw [pow_succ, IH, a_mul_a]
    congr 1
    norm_cast

theorem a_one_pow_n : (a 1 : MyQuaternionGroup n) ^ (2 * n) = 1 := by
  simp

@[simp]
theorem xa_sq (i : ZMod (2 * n)) : xa i ^ 2 = a n := by simp [sq]

@[simp]
theorem xa_pow_four (i : ZMod (2 * n)) : xa i ^ 4 = 1 := by
  calc xa i ^ 4
      = a (n + n)  := by simp [pow_succ, add_sub_assoc, sub_sub_cancel]
    _ = a ↑(2 * n) := by simp [Nat.cast_add, two_mul]
    _ = 1          := by simp


end MyQuaternionGroup
