import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

open Lean

partial def matchVecLit (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Matrix.vecEmpty _ => some []
  | Matrix.vecCons _ _ x xs => (x :: ·) <$> matchVecLit xs
  | _ => none

dsimproc vecCons_val (Matrix.vecCons _ _ _) := fun e => do
  let_expr Matrix.vecCons _ _ x xs' n := e | return .continue
  let some n := n.int? | return .continue -- The docstring claims only nat or int, but works fine for Fin
  let some xs' := matchVecLit xs' | return .continue
  let xs := x :: xs'
  let n' := (n % xs.length).toNat
  return .continue (xs[n']!)

/-- Match `Matrix.of` applied via `DFunLike.coe` to a vector-of-vectors literal,
    returning rows as lists of expressions. -/
partial def matchMatLitToVec (e : Expr) : Option (List (List Expr)) := do
  -- e should be `DFunLike.coe _ _ _ _ Matrix.of rows`
  guard (e.isAppOfArity ``DFunLike.coe 6)
  let args := e.getAppArgs
  guard (args[4]!.isAppOf ``Matrix.of)
  let rows ← matchVecLit args[5]!
  rows.mapM matchVecLit

lemma foo {a b c d : ℕ} : ![a, b, c, d, a, b, c, d, a, b, c, d] 33 = b := by dsimp
lemma bar {a b c d : ℕ} : ![a, b, c, d, a, b, c, d, a, b, c, d] (-1) = d := by simp
