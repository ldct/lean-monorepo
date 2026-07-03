import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.RowCol

/-
Helpers for matching and building matrix/vector literal expressions,
and simprocs that compute on them.
-/
open Lean

/-! ## Matching helpers -/

/-- Match a vector literal `![x₀, x₁, …]` built from `vecCons`/`vecEmpty`,
    returning the entries as a list of expressions. -/
partial def matchVecLit (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Matrix.vecEmpty _ => some []
  | Matrix.vecCons _ _ x xs => (x :: ·) <$> matchVecLit xs
  | _ => none

/-- Strip a trivial `let this := v; this` wrapper that Lean inserts around
    matrix literals written with `show`/`from`. -/
def unwrapLetE (e : Expr) : Expr :=
  match e with
  | .letE _ _ val (.bvar 0) _ => val
  | _ => e

/-- Match a `DFunLike.coe … Matrix.of rows` expression (possibly wrapped in
    `letE`), returning the raw row-vector expressions. -/
def matchMatLitRowExprs (e : Expr) : Option (List Expr) := do
  let inner := unwrapLetE e
  guard (inner.isAppOfArity ``DFunLike.coe 6)
  let args := inner.getAppArgs
  guard (args[4]!.isAppOf ``Matrix.of)
  matchVecLit args[5]!

/-- Match `Matrix.of` applied via `DFunLike.coe` to a vector-of-vectors literal,
    returning rows as lists of expressions. -/
partial def matchMatLitToVec (e : Expr) : Option (List (List Expr)) := do
  let rows ← matchMatLitRowExprs e
  rows.mapM matchVecLit

/-! ## Building helpers -/

/-- Build a `vecCons`/`vecEmpty` expression from a list of element expressions. -/
def mkVecLit (elemTy : Expr) (elems : List Expr) : Expr :=
  match elems with
  | [] => mkApp (mkConst ``Matrix.vecEmpty [levelZero]) elemTy
  | x :: xs =>
    let n := mkNatLit xs.length
    mkApp4 (mkConst ``Matrix.vecCons [levelZero]) elemTy n x (mkVecLit elemTy xs)

/-- Rebuild a matrix literal expression from `DFunLike.coe … Matrix.of rows`,
    replacing the rows vector. Preserves the original universe levels. -/
def rebuildMatLit (matExpr : Expr) (newRowsVec : Expr) : Option Expr := do
  let inner := unwrapLetE matExpr
  guard (inner.isAppOfArity ``DFunLike.coe 6)
  let fn := inner.getAppFn
  let matArgs := inner.getAppArgs
  some (mkAppN fn (matArgs.set! 5 newRowsVec))

/-! ## Simprocs -/

-- `mySimproc` simplifies `!![...] n` where `n` is a literal, extracting row `n`.
open Lean Meta Qq in
simproc_decl mySimproc (@DFunLike.coe _ _ _ _ Matrix.of _ _) := fun e => do
  let mat := (matchVecLit (e.getAppArgs[5]!)).get!
  let idx := e.getAppArgs[6]!.nat?.get!
  let proof ← mkDecideProof (← mkEq e mat[idx]!)
  return .done { expr := mat[idx]!, proof? := some proof }

-- `updateRowSimproc` simplifies `Matrix.updateRow M i v` where `M` is a matrix
-- literal, `i` is a `Fin` literal, and `v` is any expression, producing the
-- matrix with row `i` replaced by `v`.
open Lean Meta Qq in
simproc_decl updateRowSimproc (Matrix.updateRow _ _ _) := fun e => do
  guard (e.isAppOf ``Matrix.updateRow)
  let args := e.getAppArgs   -- m, n, α, DecidableEq, M, i, b
  let matExpr := args[4]!
  let some idx := args[5]!.nat? | return .continue
  let newRow := args[6]!
  let some rows := matchMatLitRowExprs matExpr | return .continue
  guard (idx < rows.length)
  let newRows := rows.set idx newRow
  let rowTy ← inferType newRow
  let newRowsVec := mkVecLit rowTy newRows
  let some result := rebuildMatLit matExpr newRowsVec | return .continue
  let proof ← mkDecideProof (← mkEq e result)
  return .done { expr := result, proof? := some proof }

/-! ## Basic smoke tests -/

example : !![1, 1, 1; 2, 2, 2; 3, 3, 3] 0 = ![1, 1, 1] := by
  simp only [mySimproc]

example : !![1, 1, 1; 2, 2, 2; 3, 3, 3] 1 = ![2, 2, 2] := by
  simp only [mySimproc]
