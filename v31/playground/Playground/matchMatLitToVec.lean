import Mathlib
import Qq

open Lean in
partial def matchVecLit (e : Expr) : Option (List Expr) :=
  match_expr e with
  | Matrix.vecEmpty _ => some []
  | Matrix.vecCons _ _ x xs => (x :: ·) <$> matchVecLit xs
  | _ => none

open Lean in
partial def matchMatLitToVec (e : Expr) : Option (List (List Expr)) := do
  -- e should be `DFunLike.coe _ _ _ _ Matrix.of rows`
  guard (e.isAppOfArity ``DFunLike.coe 6)
  let args := e.getAppArgs
  guard (args[4]!.isAppOf ``Matrix.of)
  let rows ← matchVecLit args[5]!
  rows.mapM matchVecLit

open Qq in
#eval (matchMatLitToVec (q(!![1, 1, 1; 2, 2, 2; 3, 3, 3]))).get!
