/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/


/-! # Radix AST

Core abstract syntax for the Radix DSL. The design follows a standard imperative
language structure: expressions are pure (no side effects, no function calls),
statements handle control flow and mutation, and programs bundle function
declarations with a main statement.

Key design choices:
- Expressions do not include function calls; calls are statement-level only
  (`callStmt`), which simplifies the semantics considerably.
- `scope` is the internal representation of an inlined function call: it pushes
  a fresh frame, binds parameters, executes a body, then pops the frame.
  The `inline` optimization rewrites `callStmt` into `scope`.
- Values include `addr` for heap-allocated arrays, but `addr` is not a source-level
  type -- it only appears at runtime.
-/

namespace Radix

/-! ## Types -/

/-- Radix type system. `fn` is included for potential future use but is not
currently checked by the type checker. `array` types are heap-allocated and
accessed via `addr` values at runtime. -/
inductive Ty where
  | uint64
  | bool
  | unit
  | string
  | array : Ty → Ty
  | fn : List Ty → Ty → Ty
  deriving Repr, Inhabited, BEq

/-! ## Values -/

/-- Heap address, used as a key into `Heap.store`. -/
abbrev Addr := Nat

/-- Runtime values. `addr` is not a source-level construct -- it arises only
from `alloc` at runtime. The `str` constructor wraps Lean `String` directly,
so string operations use the host string implementation. -/
inductive Value where
  | uint64 : UInt64 → Value
  | bool : Bool → Value
  | unit : Value
  | str : String → Value
  | addr : Addr → Value
  deriving Repr, Inhabited, DecidableEq, BEq

/-! ## Operators -/

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
  | strAppend
  deriving Repr, DecidableEq, Inhabited, BEq

inductive UnaryOp where
  | not | neg
  deriving Repr, DecidableEq, Inhabited, BEq

/-! ## Expressions -/

/-- Expressions are pure: they read from the environment and heap but never
modify them. No function calls -- those are statement-level. -/
inductive Expr where
  | lit : Value → Expr
  | var : String → Expr
  | binop : BinOp → Expr → Expr → Expr
  | unop : UnaryOp → Expr → Expr
  | arrGet : Expr → Expr → Expr
  | arrLen : Expr → Expr
  | strLen : Expr → Expr
  | strGet : Expr → Expr → Expr
  deriving Repr, Inhabited

/-! ## Statements -/

/-- Statements perform effects: variable mutation, heap allocation/free,
control flow, and function calls. `scope` is the frame-isolated form used
by the inliner -- it pushes a fresh frame with bound parameters, runs the
body, then pops the frame. -/
inductive Stmt where
  | skip
  | assign : String → Expr → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : Expr → Stmt → Stmt → Stmt
  | while : Expr → Stmt → Stmt
  | decl : String → Ty → Expr → Stmt
  | alloc : String → Ty → Expr → Stmt
  | free : Expr → Stmt
  | arrSet : Expr → Expr → Expr → Stmt
  | ret : Expr → Stmt
  | block : List Stmt → Stmt
  | callStmt : String → List Expr → Stmt
  | scope : List (String × Ty) → List Expr → Stmt → Stmt
  deriving Repr, Inhabited

infixr:130 " ;; " => Stmt.seq

/-! ## Function Declarations and Programs -/

/-- A function declaration. Functions are called via `Stmt.callStmt`, which
pushes a new frame, binds arguments, executes the body, then pops the frame. -/
structure FunDecl where
  name : String
  params : List (String × Ty)
  retTy : Ty
  body : Stmt
  deriving Repr, Inhabited

/-- A complete program: a list of function declarations and a main statement. -/
structure Program where
  funs : List FunDecl
  main : Stmt
  deriving Repr, Inhabited

end Radix
