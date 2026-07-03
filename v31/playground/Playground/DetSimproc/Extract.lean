import Mathlib
import Playground.DetSimproc.GaussElim

/-!
# Matrix entry extraction from Lean expressions

Extracts the `n × n` integer entries from a `Matrix (Fin n) (Fin n) ℤ` expression
by reducing `M i j` via `whnf` for each pair of indices.
-/

namespace DetSimproc
open Lean Meta Elab

/-- Build a `Fin n` literal expression for value `i` with `n` as an `Expr`. -/
def mkFinLit (n : Nat) (i : Nat) : MetaM Expr := do
  let nExpr := mkNatLit n
  let iExpr := mkNatLit i
  -- Build proof that i < n
  let ltProof ← mkDecideProof (mkApp4 (.const ``LT.lt [.zero])
    (.const ``Nat []) (.const ``instLTNat []) iExpr nExpr)
  return mkApp3 (.const ``Fin.mk []) nExpr iExpr ltProof

/-- Extract an integer value from a reduced expression.
    Handles `Int.ofNat n`, `Int.negSucc n`, `@OfNat.ofNat Int n inst`,
    `@Neg.neg Int inst (@OfNat.ofNat Int n inst)`, and raw nat lits. -/
partial def exprToInt (e : Expr) : MetaM Int := do
  let e ← whnf e
  -- Try Int.ofNat n
  if let some n := e.nat? then
    return Int.ofNat n
  match_expr e with
  | Int.ofNat n =>
    let n ← whnf n
    let some nv := n.nat? | throwError "exprToInt: expected nat lit in Int.ofNat, got {n}"
    return Int.ofNat nv
  | Int.negSucc n =>
    let n ← whnf n
    let some nv := n.nat? | throwError "exprToInt: expected nat lit in Int.negSucc, got {n}"
    return Int.negSucc nv
  | Neg.neg _ _ a =>
    let v ← exprToInt a
    return -v
  | OfNat.ofNat _ n _ =>
    let n ← whnf n
    let some nv := n.nat? | throwError "exprToInt: expected nat lit in OfNat, got {n}"
    return Int.ofNat nv
  | _ =>
    throwError "exprToInt: cannot extract integer from {e}"

/-- Build an integer literal expression. -/
def mkIntLit (z : Int) : Expr :=
  Lean.mkIntLit z

/-- Extract all entries from `M : Matrix (Fin n) (Fin n) ℤ` into an `Array (Array Int)`. -/
def extractMatrix (M : Expr) (n : Nat) : MetaM (Array (Array Int)) := do
  let mut rows : Array (Array Int) := #[]
  for i in [:n] do
    let fi ← mkFinLit n i
    let mut row : Array Int := #[]
    for j in [:n] do
      let fj ← mkFinLit n j
      -- Compute M i j
      let entry ← whnf (mkApp2 M fi fj)
      let v ← exprToInt entry
      row := row.push v
    rows := rows.push row
  return rows

/-- Match an expression of the form `Matrix.det M` where `M : Matrix (Fin n) (Fin n) ℤ`.
    Returns `(n, M)` if successful. -/
def matchMatrixDet (e : Expr) : MetaM (Option (Nat × Expr)) := do
  -- Matrix.det is `@Matrix.det n α inst M`
  match_expr e with
  | Matrix.det _ _ _ M =>
    -- Extract n from the type
    let Mty ← inferType M
    -- Mty should be `Matrix (Fin n) (Fin n) ℤ`
    match_expr Mty with
    | Matrix _ _ _ =>
      -- Get the first argument (Fin n)
      let finType := Mty.getArg! 0
      match_expr finType with
      | Fin nExpr =>
        let nExpr ← whnf nExpr
        let some n := nExpr.nat? | return none
        -- Check the scalar type is ℤ
        let scalarType := Mty.getArg! 2
        let scalarType ← whnf scalarType
        if scalarType.isConstOf ``Int then
          return some (n, M)
        else
          return none
      | _ => return none
    | _ => return none
  | _ => return none

end DetSimproc
