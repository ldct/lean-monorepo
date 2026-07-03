import Playground.DetSimproc.Lemmas
import Playground.DetSimproc.GaussElim
import Playground.DetSimproc.Extract
import Playground.DetSimproc.ProofBuilder

/-!
# `detSimproc` — a simproc for integer matrix determinants

Rewrites `M.det` (for a concrete `Matrix (Fin n) (Fin n) ℤ`) to a numeral,
producing a proof via row reduction (Gaussian elimination).

## Usage

```lean
example : E₈.det = 1 := by simp only [detSimproc]
```
-/

open Lean Meta Elab in
namespace DetSimproc

/-- The core implementation: given an expression `M.det`, compute the determinant
    and build a proof. -/
def detCore (e : Expr) : MetaM Simp.Step := do
  -- Step 1: Match Matrix.det M
  let some (n, M) ← matchMatrixDet e | return .continue
  if n == 0 then
    -- 0×0 matrix: det = 1
    let proof ← mkDecideProof (← mkEq e (mkIntLit 1))
    return .done { expr := mkIntLit 1, proof? := some proof }

  -- Step 2: Extract the n×n integer entries
  let matrix ← extractMatrix M n

  -- Step 3: Run Gaussian elimination
  let state := gaussElim matrix
  let det := computeDet state

  -- Step 4: Build proof term
  let proof ← buildProof M n state det

  -- Step 5: Return result
  let detExpr := mkIntLit det
  return .done { expr := detExpr, proof? := some proof }

end DetSimproc

open Lean Meta in
simproc_decl detSimproc (Matrix.det _) := fun e => do
  DetSimproc.detCore e
