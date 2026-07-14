import Mathlib

/-
An introduction to types and typeclass design, with motivating examples from Mathlib's algebraic hierarchy.
-/

/-
An inductive type is a type that is defined by a set of constructors, similar to algebraic data types in other programming languages.

Here, we define the type C2 with two constructors: one and neg. You can think of this as the set {1, -1}.
-/
inductive C2 : Type
  | one
  | neg
  deriving Fintype, DecidableEq

/-
The `Mul` typeclass defines how to evaluate `a * b` for elements `a` and `b`.

If you treat `C2` as the set {1, -1}, then there is one natural way to do it:

1 * 1 = 1
1 * -1 = -1
-1 * 1 = -1
-1 * -1 = 1

Here's a direct translation of the multiplication table into Lean code. As an exercise, you could try to use more advanced pattern matching syntax to define this more concisely.
-/
instance C2.instMul : Mul C2 where
  mul a b :=
    match a, b with
    | .one, .one => .one
    | .one, .neg => .neg
    | .neg, .one => .neg
    | .neg, .neg => .one

/-
Typecheck the expression C2.one * C2.neg, using the Mul C2 instance.

If you delete the `instance C2.instMul ..` line, this fails to typecheck.
-/
#check C2.one * C2.neg

/-
Evaluate the expression C2.one * C2.neg. `eval` means that the expression is compiled to C code, the C code is compiled, and then executed.
-/
#eval C2.one * C2.neg

/-
An inductive type with 3 constructors and a Mul instance. You can think of this as the group of order 3: {r⁰, r¹, r²}, which the rule r³ = r⁰.
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
Given a type G with an instance of Mul, `IsMulComm G` is the proposition that multiplication is commutative.

Here we see the use of notation typeclasses in definitions - to even *state* the proposition that multiplicatin in G is commutative, we need to know what multiplication means.
-/
abbrev IsMulComm (G) [Mul G] := ∀ a b : G, a * b = b * a


/-
For C2, we can use the `fin_cases` tactic to case on `a` and `b`.
The `rfl` tactic means that the goal is true by definition.
The `<;>` tactic combinator means "run the next tactic on each subgoal."
-/
example : IsMulComm C2 := by
  rw [IsMulComm]
  intro a b
  fin_cases a <;> fin_cases b
  <;> rfl -- each of the 4 goals can be closed by `rfl`

example : IsMulComm C3 := by
  rw [IsMulComm]
  intro a b
  fin_cases a <;> fin_cases b
  <;> rfl -- 9 goals

/-
The `decide` tactic closes such goals for `C2` and `C3`, since they are finite and have decidable equality.
You can think of this as "proof by exhaustive case analysis".
If the line `deriving Fintype, DecidableEq` is removed, this will fail.
-/
example : IsMulComm C3 := by decide

/-
In fact, we can `eval` these propositions directly. Recall that `eval` means that the expression is compiled to C code, the C code is compiled, and then executed - we can compile `∀ x : C3, ...` because C3 is finite.
-/
#eval IsMulComm C3

/-
Infinite types can have instances of `Mul`; for example, Lean's natural numbers type ℕ comes with a `Mul` instance.
-/
example : 3*4 = 12 := by rfl

/-
`grind` is a tactic that knows about the natural numbers type and their `Mul` instance.
-/
example : IsMulComm ℕ := by
  rw [IsMulComm]
  grind

/-
Given a type G with an instance of Mul, `IsMulAssoc G` is the proposition that multiplication is associative.
-/
abbrev IsMulAssoc (G) [Mul G] := ∀ a b c : G, (a * b) * c = a * (b * c)

/-
The `Mul` instances we have defined so far are all associative.
This is a hint that associativity is a more "natural" property than commutativity, even though the definition of `IsMulComm` is shorter.
-/
example : IsMulAssoc C2 := by decide
example : IsMulAssoc C3 := by decide

/-
For instance, we shall define a different multiplication on `C2` where multiplication just returns the first argument.
However, we cannot have two `Mul` instances simultaneously on the same type - if we write a * b, Lean doesn't know which `Mul` instance we meant.
To work around this, we create an namespace and overwrite the old `Mul` instance.
-/
namespace StrangeMultiplicationWorld

/-
A scoped instance to mean that this instance only applies in the `StrangeMultiplicationWorld` namespace.
-/
scoped instance : Mul C2 where
  mul a b :=
    match a, b with
    | a, _ => a

/-
This is associative, but not commutative.
-/
example : IsMulAssoc C2 := by decide
example : ¬ IsMulComm C2 := by decide

/-
Analogous instance for `ℕ`.
-/
scoped instance : Mul ℕ where
  mul a _ := a

example : 3*4 = 3 := rfl

/-
We can still prove that `ℕ, *` is associative using the `rw` tactic.
-/
example : IsMulAssoc ℕ := by
  rw [IsMulAssoc]
  intro a b c
  -- The LHS is `(a * b) * c` (the parantheses are suppressed by the pretty-printer). The `rw` tactic searches for `a * b` and replaces it with `a`.
  rw [show a * b = a by rfl]
  rw [show a * c = a by rfl]

  -- In fact, `rfl` can take multiple "steps" at once.
  rw [show a * (b * c) = a by rfl]

/-
Prove that `ℕ, *` is not commutative. `push Not` converts a `¬ ∀` goal into a `∃` goal.
-/
example : ¬ IsMulComm ℕ := by
  rw [IsMulComm]
  push Not
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
As an exercise, you can define a*b as the minimum of a and b, then show this is commutative and associative.
-/

/-
Associativity implies that the order of bracketing doesn't matter. Here is a random identity where the LHS and RHS have factors of the order but different bracketing.
-/
theorem MySemigroup.four_term_identity {G} [Mul G] (h : IsMulAssoc G) (a b c d : G) : (a * b) * (c * d) = a * (b * c) * d := by
  rw [h]
  rw [h]
  rw [h]

/-
We can define our own typeclasses using the `class` keyword.

Here, a type is an instance of `MySemigroup` if it is an instance of `Mul` and multiplication satisfies associativity.
-/
class MySemigroup (G) [Mul G] where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)

/-
The advantage is that instead of our theorems taking in `[Mul G] (h : IsMulAssoc G)` parameters, they can take in `[Mul G] [MySemigroup G]` parameters.

This theorem is now easier to state.
-/
theorem MySemigroup.four_term_identity' {G} [Mul G] [MySemigroup G] (a b c d : G) : (a * b) * (c * d) = a * (b * c) * d := by
  rw [MySemigroup.mul_assoc]
  rw [MySemigroup.mul_assoc]
  rw [MySemigroup.mul_assoc]

/-
C2 has associative multiplication, so in informal math we say "it is a semigroup".
-/
instance : MySemigroup C2 where
  mul_assoc := by decide

/-
Recall that in the conformance `inst : Mul C2`, we had to define a function `mul : C2 → C2 → C2`, i.e. provide some data. A conformance to `MySemigroup` requires us to provide a proof of `mul_assoc`.

This means `Mul` is a "data typeclass" while `MySemigroup` is a mix of data and proofs. Of course, proofs are terms of a particular type (i.e. proof is data) so this is not a formal distincition.
-/


/-
Because Lean now knows that `C2` is a semigroup, we can use the `MySemigroup.four_term_identity` theorem.
The typeclass resolution system keeps track of proof of `mul_assoc` for us, and passes it around as needed.
Replacing `C2` with `C3` will fail, because we have not shown that `C3` is a semigroup.
-/
example (a b c d : C2) : (a * b) * (c * d) = a * (b * c) * d := MySemigroup.four_term_identity' a b c d

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
Just as the concept of "associative multiplication" is split between `Mul` (function `G × G → G`) and properties (e.g. `IsMulAssoc`, `MySemigroup`), the concept of "neutral element" is split between `One` (distinguished element `1 : G`) and any properties it needs to satisfy.
The `One` typeclass carries a distinguished element `1 : G` (you can think of it as a function `(Unit) → G`) if you want) and allows the `1` notation to be used.
-/

section
/-
On its own, it's not required to satisfy any axioms; it's just a data carrier.
-/
instance : One C2 where
  one := C2.neg

/-
This is an unusual definition of `1` for `C2`.
-/
#eval (1 : C2) * C2.one
end

/- This is a much more natural choice of the distinguished element. -/
instance : One C2 where
  one := C2.one

/-
Mathlib's `Monoid` typeclass extends `One` and requires `1` to be a neutral element with respect to multiplication, i.e.
  - `1 * a = a`
  - `a * 1 = a`
-/
instance : Monoid C2 where
  mul_assoc := by decide -- `Monoid` extends `Semigroup`, not `MySemigroup`, so we need to repeat the proof of associativity.
  one_mul := by decide
  mul_one := by decide
