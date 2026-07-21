import Mathlib

namespace Exercise_2_1_1
variable {S : Type}

structure Wrap S : Type where
  ofS : S

instance : Mul (Wrap S) := ⟨fun a _ => a⟩

@[simp]
theorem mul_eq {S : Type} (a b : Wrap S) : a * b = a := rfl

instance : Semigroup (Wrap S) where
  mul_assoc a b c := by simp

-- TODO: has no identity if S is nontrivial

end Exercise_2_1_1

namespace Exercise_2_1_3

def s : ℕ → ℕ := fun n => n + 1

def f' (y₀ : ℕ) : ℕ → ℕ := fun n => match n with
  | 0 => y₀
  | .succ x => x

example (y₀ : ℕ): Function.LeftInverse (f' y₀) s := by
  intro x
  dsimp [s, f']

def leftInverses := { f : ℕ → ℕ | Function.LeftInverse f s }

example : f' 3 ∈ leftInverses := by
  simp only [leftInverses]
  intro x
  simp [f', s]

-- TODO: prove that this set has ncard ∞

end Exercise_2_1_3

namespace Exercise_2_2_2


variable {M : Type} [Monoid M]

def IsInvertible (m : M) : Prop := ∃ y, (m*y = 1 ∧ y*m = 1)

def Units : Set M := { m : M | IsInvertible m }

end Exercise_2_2_2
