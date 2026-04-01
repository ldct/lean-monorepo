import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

/-
The simproc `mySimproc` simplifies `!![...] n` where `n` is a literal
-/
open Lean

partial def matchVecLit (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Matrix.vecEmpty _ => some []
  | Matrix.vecCons _ _ x xs => (x :: ·) <$> matchVecLit xs
  | _ => none

/-- Match `Matrix.of` applied via `DFunLike.coe` to a vector-of-vectors literal,
    returning rows as lists of expressions. -/
partial def matchMatLitToVec (e : Expr) : Option (List (List Expr)) := do
  -- e should be `DFunLike.coe _ _ _ _ Matrix.of rows`
  guard (e.isAppOfArity ``DFunLike.coe 6)
  let args := e.getAppArgs
  guard (args[4]!.isAppOf ``Matrix.of)
  let rows ← matchVecLit args[5]!
  rows.mapM matchVecLit

open Lean Meta Qq in
simproc_decl mySimproc (@DFunLike.coe _ _ _ _ Matrix.of _ _) := fun e => do
  let mat := (matchVecLit (e.getAppArgs[5]!)).get!
  let idx := e.getAppArgs[6]!.nat?.get!
  logInfo m!"logged! aa={mat[idx]!}"
  let proof ← mkDecideProof (← mkEq e mat[idx]!)
  return .done { expr := mat[idx]!, proof? := some proof }

example : !![1, 1, 1; 2, 2, 2; 3, 3, 3] 0 = ![1, 1, 1] := by
  simp only [mySimproc]

example : !![1, 1, 1; 2, 2, 2; 3, 3, 3] 1 = ![2, 2, 2] := by
  simp only [mySimproc]
