import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.ZMod.Basic

/-- Dicyclic group Dicₙ (order 4n) in normal form: a^k or x a^k. -/
inductive DicyclicGroup (n : ℕ) : Type
  | a  : ZMod (2*n) → DicyclicGroup n
  | ax : ZMod (2*n) → DicyclicGroup n
  deriving DecidableEq

namespace DicyclicGroup

variable {n : ℕ}

open DicyclicGroup

def mul : DicyclicGroup n → DicyclicGroup n → DicyclicGroup n
  | a k,  a m  => a (k + m)
  | a k, ax m => ax (k + m)
  | ax k, a m => ax (k - m)
  | ax k, ax m => a (k - m + n)

instance : Mul (DicyclicGroup n) where
  mul := mul

theorem mul_eq (x y : DicyclicGroup n) : x * y = match x, y with
  | a k,  a m  => a (k + m)
  | a k, ax m => ax (k + m)
  | ax k, a m => ax (k - m)
  | ax k, ax m => a (k - m + n)
  := rfl

theorem mul_assoc : ∀ a b c : DicyclicGroup n, (a * b) * c = a * (b * c) := by
  have : (n : ZMod (2*n)) + (n : ZMod (2*n)) = 0 := by
    norm_cast
    rw [show n + n = 2 * n by ring]
    exact ZMod.natCast_self (2 * n)
  rintro (i | i) (j | j) (k | k) <;> simp [mul_eq] <;> grind

def one : DicyclicGroup n := a 0

instance : One (DicyclicGroup n) where
  one := one

def inv : DicyclicGroup n → DicyclicGroup n
  | a k => a (-k)
  | ax k => ax (n+k)

instance : Inv (DicyclicGroup n) where
  inv := inv

theorem inv_eq (g : DicyclicGroup n) : g.inv = match g with
  | a k => a (-k)
  | ax k => ax (n+k)
  := rfl

instance : Group (DicyclicGroup n) := {
  mul_assoc a b c := mul_assoc a b c
  one_mul := by
    rintro (i | i) <;> rw [show (1 : DicyclicGroup n) = DicyclicGroup.a 0 by rfl] <;> simp [mul_eq]
  mul_one := by
    rintro (i | i) <;> rw [show (1 : DicyclicGroup n) = DicyclicGroup.a 0 by rfl] <;> simp [mul_eq]
  inv a := inv a
  inv_mul_cancel := by
    have : (n : ZMod (2*n)) + (n : ZMod (2*n)) = 0 := by
      norm_cast
      rw [show n + n = 2 * n by ring]
      exact ZMod.natCast_self (2 * n)
    rintro (i | i) <;> simp [inv_eq, mul_eq, show (1 : DicyclicGroup n) = DicyclicGroup.a 0 by rfl]
    exact this
}

#min_imports

theorem center_eq (n : ℕ) : (Subgroup.center (DicyclicGroup n)).carrier = { 1, a n } := by
  sorry

end DicyclicGroup
