/-!
# Python-flavoured surface syntax

A small embedded syntax for writing imperative Lean code the way one would in
Python. It is only surface syntax: a Python `def` expands into an ordinary
`Id.run do` definition, the same code one would write by hand. See
`Playground.PairSumPython` for an example.

Supported:

* `def f(x: T, ...) -> R:` followed by an indented block,
* `x = e` (introduces `x` the first time, reassigns it afterwards),
  `x: T = e`, `x += e` and `x -= e`,
* `for x in xs:` followed by an indented block, and `return e`,
* the builtins `len(xs)`, `sum(xs)`, `range(n)` and `range(a, b)`.

Blocks are delimited by indentation, using the same column-sensitive parser
combinators (`colGt`, `many1Indent`) that Lean's own `do` blocks are built from.
-/

/-! ## Builtins

`len(`, `sum(` and `range(` are single tokens. That is what allows Python's
call syntax, since Lean's own function application needs a space (`len (xs)`). -/

macro "len(" xs:term ")" : term => `(($xs).size)
macro "sum(" xs:term ")" : term => `(($xs).sum)
macro "range(" n:term ")" : term => `([0 : $n])
macro "range(" a:term ", " b:term ")" : term => `([$a : $b])

/-! ## Statements -/

declare_syntax_cat pystmt

/-- `x = e` introduces `x` on its first assignment and reassigns it afterwards. -/
syntax ident " = " term : pystmt
/-- An annotated assignment `x: T = e`. Annotations matter more than in Python,
as Lean reads a bare `0` as a `Nat`. -/
syntax ident ": " term:51 " = " term : pystmt
syntax ident " += " term : pystmt
syntax ident " -= " term : pystmt
/-- A `for` loop; the body is the block that follows, indented further than
the `for` (`colGt`). -/
syntax "for " ident " in " term ":" colGt many1Indent(pystmt) : pystmt
syntax "return " term : pystmt

section
open Lean

/-- Translate a block of Python statements into `do` elements.

`bound` holds the variables already assigned in an enclosing block: assigning
to one of those is a reassignment (`x := e`), while the first assignment to any
other name introduces it (`let mut x := e`). Unlike in Python, a variable first
assigned inside a loop body is local to that body. -/
partial def pyBlock (bound : Array Name) (stmts : Array (TSyntax `pystmt)) :
    MacroM (Array (TSyntax `doElem)) := do
  let mut bound := bound
  let mut elems : Array (TSyntax `doElem) := #[]
  for stmt in stmts do
    -- `withRef` makes errors in the generated code point at this statement.
    let (elem, introduced) ← withRef stmt do
      match stmt with
      | `(pystmt| $x:ident : $ty = $e) =>
        return (← `(doElem| let mut $x:ident : $ty := $e), some x.getId)
      | `(pystmt| $x:ident = $e) =>
        if bound.contains x.getId then
          return (← `(doElem| $x:ident := $e), none)
        else
          return (← `(doElem| let mut $x:ident := $e), some x.getId)
      | `(pystmt| $x:ident += $e) =>
        return (← `(doElem| $x:ident := $x + $e), none)
      | `(pystmt| $x:ident -= $e) =>
        return (← `(doElem| $x:ident := $x - $e), none)
      | `(pystmt| for $x:ident in $xs : $body:pystmt*) =>
        let inner ← pyBlock bound body
        -- A `range` loop binds a hidden `h : x ∈ xs`, which is what lets `A[i]`
        -- discharge its bounds check. Other loops expand to a plain `for`.
        let isRange := match xs with
          | `(range($_)) => true
          | `(range($_, $_)) => true
          | _ => false
        let loop ← if isRange then
          `(doElem| for h : $x:ident in $xs do $[$inner:doElem]*)
        else
          `(doElem| for $x:ident in $xs do $[$inner:doElem]*)
        return (loop, none)
      | `(pystmt| return $e) =>
        return (← `(doElem| return $e), none)
      | _ => Macro.throwError "unsupported Python statement"
    elems := elems.push elem
    if let some x := introduced then
      bound := bound.push x
  return elems

/-! ## Functions -/

declare_syntax_cat pyparam
syntax ident ": " term : pyparam

/-- `def f(x: T, ...) -> R:` followed by an indented block.

This shares the `def` keyword with Lean's own definitions. Lean keeps whichever
parse consumes more input, and an ordinary definition never has the `->`, so
ordinary definitions are unaffected. -/
syntax "def " ident "(" pyparam,* ")" " -> " term ":" colGt many1Indent(pystmt) : command

macro_rules
  | `(command| def $name:ident ($params:pyparam,*) -> $ret : $body:pystmt*) => do
    let elems ← pyBlock #[] body
    let mut val ← `(Id.run do $[$elems:doElem]*)
    let mut ty := ret
    for param in params.getElems.reverse do
      let `(pyparam| $x:ident : $t) := param | Macro.throwUnsupported
      val ← `(fun $x:ident => $val)
      ty ← `($t → $ty)
    `(command| def $name:ident : $ty := $val)

end
