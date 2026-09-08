/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Expr

/-! # Radix Fuel-Based Interpreter

Executable interpreter using fuel to guarantee termination. This is the
"runnable" counterpart to the relational `BigStep` semantics -- useful for
testing and `#guard` assertions, and the subject of the interpreter
correctness proofs (`Radix.Proofs.InterpCorrectness`).

The interpreter returns `Except String (Option Value) × PState`:
- `.ok none` means normal completion
- `.ok (some v)` means a `ret` was encountered with value `v`
- `.error msg` means a runtime error
-/

namespace Radix

def evalExpr (e : Expr) (σ : PState) : Except String Value :=
  match e.eval σ with
  | some v => .ok v
  | none => .error "failed to evaluate expression"

def evalArgs (args : List Expr) (σ : PState) : Except String (List Value) :=
  args.mapM (fun e => evalExpr e σ)

def mkFrame (params : List (String × Ty)) (args : List Value) : Except String Frame := do
  if params.length ≠ args.length then
    throw s!"arity mismatch: expected {params.length} args, got {args.length}"
  let env := (params.zip args).foldl (fun e (p, v) => e.set p.1 v) Env.empty
  return { env }

/-- Result type for the interpreter: either success with optional return value
and final state, or an error message. -/
abbrev InterpResult := Except String (Option Value) × PState

/-- Helper: thread a successful non-returning result into a continuation. -/
@[inline] def andThen (r : InterpResult) (k : PState → InterpResult) : InterpResult :=
  match r with
  | (.ok none, σ') => k σ'
  | (.ok (some v), σ') => (.ok (some v), σ')
  | (.error e, σ') => (.error e, σ')

/-- Fuel-based interpreter. Returns `(.ok none, σ')` for normal completion,
`(.ok (some v), σ')` when a `ret` statement is reached, or `(.error msg, σ)` on error. -/
def Stmt.interp (fuel : Nat) (s : Stmt) (σ : PState) : InterpResult :=
  match fuel with
  | 0 => (.error "out of fuel", σ)
  | fuel + 1 =>
    match s with
    | .skip => (.ok none, σ)

    | .assign x e =>
      match evalExpr e σ with
      | .error msg => (.error msg, σ)
      | .ok v =>
        match σ.setVar x v with
        | some σ' => (.ok none, σ')
        | none => (.error "assign: no active frame", σ)

    | .decl x _ty e =>
      match evalExpr e σ with
      | .error msg => (.error msg, σ)
      | .ok v =>
        match σ.setVar x v with
        | some σ' => (.ok none, σ')
        | none => (.error "decl: no active frame", σ)

    | .seq s₁ s₂ =>
      andThen (s₁.interp fuel σ) (s₂.interp fuel)

    | .ite c t f =>
      match evalExpr c σ with
      | .error msg => (.error msg, σ)
      | .ok (.bool true) => t.interp fuel σ
      | .ok (.bool false) => f.interp fuel σ
      | _ => (.error "if: condition must be bool", σ)

    | .while c b =>
      match evalExpr c σ with
      | .error msg => (.error msg, σ)
      | .ok (.bool true) =>
        andThen (b.interp fuel σ) (s.interp fuel)
      | .ok (.bool false) => (.ok none, σ)
      | _ => (.error "while: condition must be bool", σ)

    | .alloc x _ty szExpr =>
      match evalExpr szExpr σ with
      | .error msg => (.error msg, σ)
      | .ok (.uint64 sz) =>
        let (a, heap') := σ.heap.alloc (Array.replicate sz.toNat (.uint64 0))
        let σ' := { σ with heap := heap' }
        match σ'.setVar x (.addr a) with
        | some σ'' => (.ok none, σ'')
        | none => (.error "alloc: no active frame", σ)
      | _ => (.error "alloc: size must be uint64", σ)

    | .free e =>
      match evalExpr e σ with
      | .error msg => (.error msg, σ)
      | .ok (.addr a) =>
        match σ.heap.free a with
        | some heap' => (.ok none, { σ with heap := heap' })
        | none => (.error s!"free: invalid address {a}", σ)
      | _ => (.error "free: expected address", σ)

    | .arrSet arr idx val =>
      match evalExpr arr σ, evalExpr idx σ, evalExpr val σ with
      | .ok (.addr a), .ok (.uint64 i), .ok vv =>
        match σ.heap.write a i.toNat vv with
        | some heap' => (.ok none, { σ with heap := heap' })
        | none => (.error s!"arrSet: write failed at addr {a} index {i}", σ)
      | .error msg, _, _ => (.error msg, σ)
      | _, .error msg, _ => (.error msg, σ)
      | _, _, .error msg => (.error msg, σ)
      | _, _, _ => (.error "arrSet: expected address and uint64 index", σ)

    | .ret e =>
      match evalExpr e σ with
      | .error msg => (.error msg, σ)
      | .ok v => (.ok (some v), σ)

    | .block stmts =>
      (stmts.foldl (· ;; ·) .skip).interp fuel σ

    | .callStmt name args =>
      match σ.lookupFun name with
      | none => (.error s!"undefined function: {name}", σ)
      | some fd =>
        match evalArgs args σ with
        | .error msg => (.error msg, σ)
        | .ok vs =>
          match mkFrame fd.params vs with
          | .error msg => (.error msg, σ)
          | .ok frame =>
            let σ₁ := σ.pushFrame frame
            match fd.body.interp fuel σ₁ with
            | (.error msg, _) => (.error msg, σ)
            | (.ok _, σ₂) =>
              match σ₂.popFrame with
              | some (_, σ₃) => (.ok none, σ₃)
              | none => (.error "callStmt: frame stack underflow", σ)

    | .scope params args body =>
      match evalArgs args σ with
      | .error msg => (.error msg, σ)
      | .ok vs =>
        match mkFrame params vs with
        | .error msg => (.error msg, σ)
        | .ok frame =>
          let σ₁ := σ.pushFrame frame
          match body.interp fuel σ₁ with
          | (.error msg, _) => (.error msg, σ)
          | (.ok _, σ₂) =>
            match σ₂.popFrame with
            | some (_, σ₃) => (.ok none, σ₃)
            | none => (.error "scope: frame stack underflow", σ)
termination_by fuel

/-- Run a program with the given fuel. -/
def Program.run (p : Program) (fuel : Nat := 1000) : Except String PState :=
  let σ := PState.initFromProgram p
  match p.main.interp fuel σ with
  | (.ok _, σ') => .ok σ'
  | (.error msg, _) => .error msg

/-- Run a standalone statement with initial state. -/
def Stmt.run (s : Stmt) (fuel : Nat := 1000) : Except String PState :=
  match s.interp fuel {} with
  | (.ok _, σ') => .ok σ'
  | (.error msg, _) => .error msg

end Radix
