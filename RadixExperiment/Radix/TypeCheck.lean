/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.AST
import Std.Data.HashMap

/-! # Radix Type Checking

Type inference for Radix expressions. Given a type environment `TyEnv`
(mapping variable names to types) and function signatures `FunSigs`,
`Expr.typeOf` infers the type of an expression or returns `none` if
the expression is ill-typed.

This module defines the typing rules used by the type safety proofs in
`Radix.Proofs.TypeSafety`. Statement-level type checking is not
implemented -- the current focus is expression-level preservation.
-/

namespace Radix
open Std

/-- Type environment: maps variable names to their declared types. -/
abbrev TyEnv := HashMap String Ty

/-- Function signature table: maps function names to (parameter types, return type). -/
abbrev FunSigs := HashMap String (List Ty × Ty)

@[simp] def BinOp.typeOfResult : BinOp → Ty → Ty → Option Ty
  | .add, .uint64, .uint64 | .sub, .uint64, .uint64
  | .mul, .uint64, .uint64 | .div, .uint64, .uint64
  | .mod, .uint64, .uint64 => some .uint64
  | .eq, a, b | .ne, a, b => if a == b then some .bool else none
  | .lt, .uint64, .uint64 | .le, .uint64, .uint64
  | .gt, .uint64, .uint64 | .ge, .uint64, .uint64 => some .bool
  | .and, .bool, .bool | .or, .bool, .bool => some .bool
  | .strAppend, .string, .string => some .string
  | _, _, _ => none

@[simp] def UnaryOp.typeOfResult : UnaryOp → Ty → Option Ty
  | .not, .bool => some .bool
  | .neg, .uint64 => some .uint64
  | _, _ => none

/-- Infer the type of an expression. -/
def Expr.typeOf (Γ : TyEnv) (sigs : FunSigs) : Expr → Option Ty
  | .lit (.uint64 _) => some .uint64
  | .lit (.bool _) => some .bool
  | .lit .unit => some .unit
  | .lit (.str _) => some .string
  | .lit (.addr _) => none
  | .var x => Γ.get? x
  | .binop op l r => do
    let tl ← l.typeOf Γ sigs
    let tr ← r.typeOf Γ sigs
    op.typeOfResult tl tr
  | .unop op e => do
    let t ← e.typeOf Γ sigs
    op.typeOfResult t
  | .arrGet arr idx => do
    let .array elemTy ← arr.typeOf Γ sigs | none
    let .uint64 ← idx.typeOf Γ sigs | none
    some elemTy
  | .arrLen arr => do
    let .array _ ← arr.typeOf Γ sigs | none
    some .uint64
  | .strLen s => do
    let .string ← s.typeOf Γ sigs | none
    some .uint64
  | .strGet s idx => do
    let .string ← s.typeOf Γ sigs | none
    let .uint64 ← idx.typeOf Γ sigs | none
    some .string

end Radix
