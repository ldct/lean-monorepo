# Python syntax: notes for future extensions

How to grow `PythonSyntax.lean` from the two functions in
`PairSumPython.lean` into a larger subset of Python.

**Status:** the Python syntax files have not been compiled yet (no Lean
toolchain was available when they were written). Run
`lake build Playground.PairSumPython` and fix what breaks before extending.

## Keep the whole-function translator

Python decides which variables exist per function, not per block, so some
statements can only be translated by something that sees the whole function.
`pyBlock` already tracks which names are bound. Per-statement macros (the
approach in the ChatGPT version) cannot. For example:

```python
if n > 0:
    sign = 1
else:
    sign = -1
return sign
```

A `let mut sign` in each branch is local to that branch in Lean, so the
translation has to declare `sign` above the `if`. The same goes for
`global`/`nonlocal`, and for variables first assigned inside a loop and used
after it (currently local to the loop, see `pyBlock`'s docstring). Declaring
a variable early needs its type or an initial value: either require an
annotation, or default to `Int` once literals are translated as `Int` (see
below).

## Ideas from the ChatGPT version

- **A dedicated keyword such as `pydef`** instead of overloading `def`. The
  overload works today because a Python header always contains `->`. Default
  arguments, keyword arguments or decorators would make the two grammars
  overlap more, and parse errors would get confusing.
- **A `python:` term**, so a Python body can sit under an ordinary Lean
  signature: `def f (A : Array Int) : Int := python: ...`.
- **A macro fallback for unknown statements** (their `pyStmt%` bridge into
  `do`). Context-free additions then take one `macro_rules` line each instead
  of another case in `pyBlock`. Candidates: `elif`, `pass`, `break`,
  `continue`, `a, b = b, a`, and more augmented assignments (`*=`, `//=`,
  `%=`).

## A separate expression category

Both versions reuse Lean's `term` for Python expressions. That won't scale:

- **Builtins clash with Lean names.** The ChatGPT version reserves `len`,
  `sum` and `range` as keywords. Doing the same for `min`, `max` or `abs`
  would break ordinary Lean code in any file that imports the syntax. Our
  `len(`-style tokens are narrower but still global.
- **Operators mean different things:** `//`, `**`, `/` (true division),
  `and`/`or`/`not`, chained comparisons `a < b < c`, negative indices `A[-1]`,
  slicing `A[i:j]`.
- **Literals:** a bare `0` is a `Nat` in Lean, hence `total: Int = 0`.

Plan: `declare_syntax_cat pyexpr (behavior := both)`, translated by a function
like statements are. In a category with `behavior := both`, the first word of
a rule (such as `len`) is not reserved globally. That's the same mechanism
that keeps tactic names from being keywords. Translating every integer literal
as `(n : Int)` removes most annotations.

Comprehensions belong here too.
`sum(A[i] * A[j] for i in range(len(A)) for j in range(len(A)) if i < j)`
maps onto the `List` monad, as in `ansSpec'`.

## When to switch from a macro to an elaborator

Macros can't see types. Anything type-directed needs the translator to run as
an elaborator (`TermElabM`/`CommandElabM`) instead of in `MacroM`:

- `len`, `sum` and indexing on lists, arrays and strings alike,
- `/` producing a `Float` or `Rat`,
- inferring the type of a variable declared early from how it's used,
- deciding when a loop needs a bounds proof, instead of the current rule
  ("only `range(...)` loops").

## Loops and proofs

- **`while`:** Lean's `while` in `Id.run do` has no termination proof (it's
  built on `Loop`), so nothing can be proved about functions that use it. For
  proofs, translate `while` with a fuel argument or a decreasing measure.
- **The generated code shapes the proofs.** Today the Python definitions
  expand to the same `do` code a person would write (`Py.ans1 = ans1` and
  `Py.ans5 = ans5` by `rfl`), so existing proofs carry over. Declaring
  variables early or adding bounds proofs changes the generated code, and
  proofs about it would change with it.
