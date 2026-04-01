import Mathlib

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

def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

variable {n : Type*} [Fintype n] [DecidableEq n] in
lemma my_helper {M : Matrix n n ℤ} {k : ℤ} (i j : n) (a b : ℤ)
    (h : (M.updateRow i (a • M i + b • M j)).det = a * k)
    (hij : i ≠ j := by decide) (ha : a ≠ 0 := by decide) :
    M.det = k := by
  simpa only [M.det_updateRow_add, M.det_updateRow_smul, M.det_updateRow_eq_zero hij.symm,
    M.updateRow_eq_self, add_zero, mul_zero, mul_eq_mul_left_iff, ha, or_false] using h

set_option linter.flexible false in
theorem E₈_det : E₈.det = 1 := by
  apply my_helper 2 0 (2:ℤ) (1:ℤ)
  simp [E₈, updateRowSimproc, mySimproc]
  apply my_helper 3 1 (2:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 3 2 (3:ℤ) (2:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 4 3 (5:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 5 4 (4:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 6 5 (3:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  apply my_helper 7 6 (2:ℤ) (1:ℤ)
  simp [updateRowSimproc, mySimproc]
  rw [Matrix.det_of_upperTriangular]
  · decide +kernel
  · unfold Matrix.BlockTriangular; decide +kernel
