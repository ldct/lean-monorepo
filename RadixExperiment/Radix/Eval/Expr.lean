/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.State

/-! # Radix Expression Evaluation

Defines evaluation for binary operators, unary operators, and expressions.
All operations return `Option Value` -- `none` means a runtime error
(type mismatch, division by zero, out-of-bounds access, etc.).

Expression evaluation is pure: it reads from the program state but never
modifies it. This separation is what makes the optimization correctness
proofs tractable -- expression-level rewrites only need to preserve
`Expr.eval`, not the full `BigStep` relation.
-/

namespace Radix

/-- Evaluate a binary operator. Returns `none` on type mismatch or division
by zero. Marked `@[simp]` so the optimization correctness proofs can
reduce concrete cases automatically. -/
@[simp] def BinOp.eval : BinOp → Value → Value → Option Value
  | .add, .uint64 a, .uint64 b => some (.uint64 (a + b))
  | .sub, .uint64 a, .uint64 b => some (.uint64 (a - b))
  | .mul, .uint64 a, .uint64 b => some (.uint64 (a * b))
  | .div, .uint64 a, .uint64 b => if b = 0 then none else some (.uint64 (a / b))
  | .mod, .uint64 a, .uint64 b => if b = 0 then none else some (.uint64 (a % b))
  | .eq,  a,         b         => some (.bool (a == b))
  | .ne,  a,         b         => some (.bool (a != b))
  | .lt,  .uint64 a, .uint64 b => some (.bool (a < b))
  | .le,  .uint64 a, .uint64 b => some (.bool (a ≤ b))
  | .gt,  .uint64 a, .uint64 b => some (.bool (a > b))
  | .ge,  .uint64 a, .uint64 b => some (.bool (a ≥ b))
  | .and, .bool a,   .bool b   => some (.bool (a && b))
  | .or,  .bool a,   .bool b   => some (.bool (a || b))
  | .strAppend, .str a, .str b => some (.str (a ++ b))
  | _, _, _ => none

@[simp] def UnaryOp.eval : UnaryOp → Value → Option Value
  | .not, .bool b   => some (.bool !b)
  | .neg, .uint64 n => some (.uint64 (0 - n))
  | _, _ => none

/-- Evaluate an expression in a program state. Function calls are not handled
here — they require the statement-level evaluator. -/
def Expr.eval (σ : PState) : Expr → Option Value
  | .lit v => some v
  | .var x => σ.getVar x
  | .binop op l r => do
    let vl ← l.eval σ
    let vr ← r.eval σ
    op.eval vl vr
  | .unop op e => do
    let v ← e.eval σ
    op.eval v
  | .arrGet arr idx => do
    let .addr a ← arr.eval σ | none
    let .uint64 i ← idx.eval σ | none
    σ.heap.read a i.toNat
  | .arrLen arr => do
    let .addr a ← arr.eval σ | none
    let sz ← σ.heap.arraySize a
    some (.uint64 sz.toUInt64)
  | .strLen s => do
    let .str sv ← s.eval σ | none
    some (.uint64 sv.length.toUInt64)
  | .strGet s idx => do
    let .str sv ← s.eval σ | none
    let .uint64 i ← idx.eval σ | none
    if i.toNat < sv.length then
      some (.str (String.Pos.Raw.get sv ⟨i.toNat⟩ |>.toString))
    else
      none


end Radix
