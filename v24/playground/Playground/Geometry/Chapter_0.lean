import Mathlib

/-
An introduction to inductive types, notation typeclasses, data typeclasses
-/

set_option linter.style.longLine false

/-
An inductive type is a type that is defined by a set of constructors, similar to algebraic data types in other programming languages.

Here, we define the type C2 with two constructors: one and neg. You can think of this as the set {1, -1}.
-/
inductive C2 : Type
  | one
  | neg
  deriving Fintype, DecidableEq

/-
The `Mul` typeclass defines how to evaluate `a * b` for elements `a` and `b`. You can think of this as the operation of multiplication:

1 * 1 = 1
1 * -1 = -1
-1 * 1 = -1
-1 * -1 = 1

Lean's pattern matching syntax allows us to define the first two cases together
-/
instance : Mul C2 where
  mul a b :=
    match a, b with
    | .one, x => x
    | x, .one => x
    | .neg, .neg => .one

/-
Typecheck and evaluate the expression C2.one * C2.neg, using the Mul C2 instance.
-/
#check C2.one * C2.neg
#eval C2.one * C2.neg

/-
An inductive type with 3 constructors and a Mul instance. You can think of this as the set {r⁰, r¹, r²}.
-/
inductive C3 : Type
  | r0
  | r1
  | r2
  deriving Fintype, DecidableEq

instance : Mul C3 where
  mul a b :=
    match a, b with
    | .r0, x => x
    | x, .r0 => x
    | .r1, .r1 => .r2
    | .r2, .r2 => .r1
    | .r1, .r2 => .r0
    | .r2, .r1 => .r0

/-
Given a type G with an instance of Mul, `HasCommMul G` is the proposition that multiplication is commutative.
-/
abbrev HasCommMul (G) [Mul G] := ∀ a b : G, a * b = b * a


/-
For C2, we can use the `fin_cases` tactic to case on `a` and `b`.
The `rfl` tactic means that the goal is true by definition.
The `<;>` tactic combinator means "run the next tactic on each subgoal."
-/
example : HasCommMul C2 := by
  rw [HasCommMul]
  intro a b
  fin_cases a <;> fin_cases b
  <;> rfl -- each of the 4 goals can be closed by `rfl`

example : HasCommMul C3 := by
  rw [HasCommMul]
  intro a b
  fin_cases a <;> fin_cases b
  <;> rfl -- 9 goals

/-
The `decide` tactic closes such goals for `C2` and `C3`, since they are finite and have decidable equality.
As a simplification, you can think of this as "proof by exhaustive case analysis".
-/
example : HasCommMul C3 := by decide

/-
In fact, we can `eval` these propositions directly.
-/
#eval HasCommMul C3

/-
Infinite types can have instances of `Mul`; for example, Lean's natural numbers type ℕ comes with a `Mul` instance.
-/
example : 3*4 = 12 := by rfl

/-
`grind` is a tactic that knows about the natural numbers type and their `Mul` instance.
-/
example : HasCommMul ℕ := by
  rw [HasCommMul]
  grind

/-
Given a type G with an instance of Mul, `HasAssocMul G` is the proposition that multiplication is associative.
-/
abbrev HasAssocMul (G) [Mul G] := ∀ a b c : G, (a * b) * c = a * (b * c)

/-
The `Mul` instances we have defined so far are all associative.
This is a hint that associativity is a more "natural" property than commutativity, even though the definition of `HasCommMul` is shorter.
-/
example : HasAssocMul C2 := by decide
example : HasAssocMul C3 := by decide

/-
For instance, we shall define a different multiplication on `C2` where multiplication just returns the first argument.
To avoid overriding the existing `Mul` instance, we create an namespace
-/
namespace StrangeMultiplicationWorld

/-
We used a scoped instance to mean that this instance only applies in the `StrangeMultiplicationWorld` namespace.
-/
scoped instance : Mul C2 where
  mul a b :=
    match a, b with
    | a, _ => a

/-
This is associative, but not commutative.
-/
example : HasAssocMul C2 := by decide
example : ¬ HasCommMul C2 := by decide

scoped instance : Mul ℕ where
  mul a _ := a

example : 3*4 = 3 := rfl

/-
We can still prove that `ℕ, *` is associative using the `rw` tactic.
-/
example : HasAssocMul ℕ := by
  rw [HasAssocMul]
  intro a b c
  -- The LHS is `(a * b) * c` (the parantheses are suppressed by the pretty-printer). The `rw` tactic searches for `a * b` and replaces it with `a`.
  rw [show a * b = a by rfl]
  rw [show a * c = a by rfl]

  -- We can actually evaluate this in a single step. In fact, after `intro a b c`, `rfl` closes the goal.
  rw [show a * (b * c) = a by rfl]

/-
Prove that `ℕ, *` is not commutative. `push_neg` converts a `¬ ∀` goal into a `∃` goal.
-/
example : ¬ HasCommMul ℕ := by
  rw [HasCommMul]
  push_neg
  use 3, 4
  rw [show 3 * 4 = 3 by rfl]
  rw [show 4 * 3 = 4 by rfl]
  norm_num

end StrangeMultiplicationWorld

/-
Back to normal
-/
example : 3*4 = 12 := by rfl

/-
Exercise: Define a*b as the minimum of a and b, then show this is commutative and associative.
-/

/-
We can define our own typeclasses. Here, a type is an instance of `MySemigroup` if it is an instance of `Mul` and multiplication satisfies associativity.
This way, instead of our theorems taking in `[Mul G] (h : HasAssocMul G)` parameters, they can take in `[Mul G] [MySemigroup G]` parameters.
-/
class MySemigroup (G) [Mul G] where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)

/-
This theorem is now easier to state.
-/
theorem MySemigroup.four_term_identity {G} [Mul G] [MySemigroup G] (a b c d : G) : (a * b) * (c * d) = a * (b * c) * d := by
  rw [MySemigroup.mul_assoc]
  rw [MySemigroup.mul_assoc]
  rw [MySemigroup.mul_assoc]

instance : MySemigroup C2 where
  mul_assoc := by decide

/-
Because Lean now knows that `C2` is a semigroup, we can use the `MySemigroup.four_term_identity` theorem.
Essentially, the typeclass resolution system keeps track of proof of `mul_assoc` for us, and passes it around as needed.
Replacing `C2` with `C3` will fail, because we have not shown that `C3` is a semigroup.
-/
example (a b c d : C2) : (a * b) * (c * d) = a * (b * c) * d := MySemigroup.four_term_identity a b c d

/-
The synth command shows the result of typeclass inference.
-/
#synth MySemigroup C2

/-
You can use this to look up the group structure on the type `Equiv.Perm ℝ`, the permutations of the real numbers.
-/
#synth Group (Equiv.Perm ℝ)
#check Equiv.Perm.permGroup

/-
Next we'd like to express the fact that `C2` has a distingushed element `.one` that is "neutral".
Just as the concept of "associative multiplication" is split between `Mul` (function `G × G → G`) and properties (e.g. `HasAssocMul`, `MySemigroup`), the concept of "neutral element" is split between `One` (distinguished element `1 : G`) and any properties it needs to satisfy.
The `One` typeclass carries a distinguished element `1 : G` (you can think of it as a function `(Unit) → G`) if you want) and allows the `1` notation to be used.
-/

namespace StrangeOneWorld

/-
On its own, it's not required to satisfy any axioms; it's just a data carrier.
-/
instance : One C2 where
  one := C2.neg

/-
This is an unusual definition of `1` for `C2`.
-/
#eval (1 : C2) * C2.one
end StrangeOneWorld

/-
Mathlib's `Monoid` typeclass extends `One` and requires `1` to be a neutral element.
-/
instance : Monoid C2 where
  mul_assoc := by decide
  one := C2.one
  one_mul := by decide
  mul_one := by decide
