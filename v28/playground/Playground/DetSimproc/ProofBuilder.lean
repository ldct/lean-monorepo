import Mathlib
import Playground.DetSimproc.Lemmas
import Playground.DetSimproc.GaussElim
import Playground.DetSimproc.Extract

/-!
# Proof term builder for determinant computation

Given the row operations from Gaussian elimination, builds a proof term
that `M.det = k` by chaining applications of `det_rowCombine`, `det_rowSwap`,
and `det_upperTriangular_eq`.
-/

open Lean Meta Elab in
namespace DetSimproc

/-- Build a proof of `p` using `decide`. -/
def mkDecide (p : Expr) : MetaM Expr := do
  mkDecideProof p

/-- Build a `Fin n` literal as an expression, where `n` is fixed. -/
def mkFinExpr (nNat : Nat) (i : Nat) : MetaM Expr := do
  mkFinLit nNat i

/-- Build the full proof that `M.det = k`.

  Strategy: we work through the ops list forward. At each step we know:
  - The "current matrix" (the one after all previous ops have been applied)
    is implicitly the LHS of the goal we're building.
  - We need to construct a proof from the inside out.

  Actually, we build the proof from the **inside out** (last op first).
  The innermost proof is the base case (upper triangular).
  Each outer layer wraps it with `det_rowCombine` or `det_rowSwap`.
-/
def buildProof (M : Expr) (n : Nat) (state : GaussState) (det : Int) : MetaM Expr := do
  let nExpr := mkNatLit n
  let intTy := mkConst ``Int
  -- The matrix type
  let finN := mkApp (.const ``Fin []) nExpr
  let matTy := mkApp3 (.const ``Matrix [.zero, .zero, .zero]) finN finN intTy

  -- We'll build expressions for intermediate matrices.
  -- Start from the final matrix and work backwards.
  -- First, compute all intermediate matrices as expressions.

  -- Actually, the simpler approach: build the proof term and let Lean's
  -- elaborator figure out the intermediate matrices via unification.

  -- We need to be more careful. Let's build the proof from inside out.
  -- The ops are stored in order (first op applied first).
  -- We need to reverse them.

  let ops := state.ops

  -- Compute what `k` should be at each level.
  -- If ops are [op1, op2, ..., opN], then:
  -- - After all ops, det(final) = diagProd (with sign from swaps)
  -- - Before opN: k_N such that det(matrix_before_opN) = k_N
  -- - Before opN-1: k_{N-1} such that det(matrix_before_{N-1}) = k_{N-1}
  -- - ...
  -- - Before op1: k_0 = det (the answer)

  -- For a combine(i,j,a,b): det(before) = k  iff  det(after) = a * k
  -- For a swap(i,j): det(before) = k  iff  det(after) = -k

  -- So working forward:
  -- k_0 = det
  -- After op1 (combine a1): k_1 = a1 * k_0
  -- After op2 (combine a2): k_2 = a2 * k_1
  -- ...
  -- k_final = diagProd (accounting for sign)

  -- Working backward from k_final:
  -- k_{N} = diagProd
  -- k_{N-1} = k_N / a_N (for combine with scale a_N)
  -- etc.

  -- Let's compute k values forward:
  let mut kValues : Array Int := #[det]
  for op in ops do
    let prevK := kValues.back!
    match op with
    | .combine _ _ a _ => kValues := kValues.push (a * prevK)
    | .swap _ _ => kValues := kValues.push (-prevK)
  -- kValues[0] = det, kValues[ops.size] = diagProd of final matrix

  -- The base case proves: finalMatrix.det = kValues[ops.size]
  -- Then we wrap each op working backwards.

  -- Step 1: Build expressions for the intermediate matrices
  -- We need to compute the actual matrix expressions.
  -- M_0 = M (the original)
  -- M_1 = M_0.updateRow i (a • M_0 i + b • M_0 j)  (for combine)
  -- M_1 = M_0.submatrix (Equiv.swap i j) id  (for swap)
  -- etc.

  let mut matExprs : Array Expr := #[M]
  for op in ops do
    let prevM := matExprs.back!
    match op with
    | .combine i j a b => do
      let fi ← mkFinExpr n i
      let fj ← mkFinExpr n j
      let aExpr := mkIntLit a
      let bExpr := mkIntLit b
      -- M.updateRow i (a • M i + b • M j)
      -- M i : Fin n → ℤ
      let Mi := mkApp prevM fi  -- this is `M i` as a function `Fin n → ℤ`
      let Mj := mkApp prevM fj
      -- a • M i : we need HSMul.hSMul a (M i)
      let rowTy := mkApp2 (.const ``Pi [.zero]) finN (mkApp (.const ``fun []) intTy)
      -- Actually, let's use Lean's elaboration. The terms are:
      -- @Matrix.updateRow (Fin n) (Fin n) ℤ M i (a • M i + b • M j)
      -- We need the SMul and Add instances.
      -- Simpler: just build the updateRow application and let Lean fill instances.

      -- HAdd.hAdd (HSMul.hSMul a (M i)) (HSMul.hSMul b (M j))
      let sMulInst ← synthInstance (← mkAppM ``SMul #[intTy, ← mkArrowN #[finN] intTy])
      let addInst ← synthInstance (← mkAppM ``Add #[← mkArrowN #[finN] intTy])
      let aMi ← mkAppM ``HSMul.hSMul #[aExpr, Mi]
      let bMj ← mkAppM ``HSMul.hSMul #[bExpr, Mj]
      let sum ← mkAppM ``HAdd.hAdd #[aMi, bMj]
      let newM ← mkAppM ``Matrix.updateRow #[prevM, fi, sum]
      matExprs := matExprs.push newM
    | .swap i j => do
      let fi ← mkFinExpr n i
      let fj ← mkFinExpr n j
      let swapEquiv ← mkAppM ``Equiv.swap #[fi, fj]
      let newM ← mkAppM ``Matrix.submatrix #[prevM, swapEquiv, mkConst ``id [.zero]]
      matExprs := matExprs.push newM

  -- Step 2: Build the base case proof
  -- Prove: matExprs.back!.det = kValues.back!
  -- Using det_upperTriangular_eq
  let finalM := matExprs.back!
  let finalK := kValues.back!
  let finalKExpr := mkIntLit finalK

  -- Build BlockTriangular proof by decide
  let blockTriProp ← mkAppM ``Matrix.BlockTriangular #[finalM, mkConst ``id [.zero]]
  let blockTriProof ← mkDecide blockTriProp

  -- Build diagonal product proof by decide
  -- ∏ i : Fin n, finalM.diag i = finalK
  let diagExpr ← mkAppM ``Matrix.diag #[finalM]
  let prodExpr ← mkAppM ``Finset.univ.prod (fun i => mkApp diagExpr i)
  -- Actually, let's build: (∏ i : Fin n, M.diag i) = k
  -- Finset.prod Finset.univ (fun i => M.diag i)
  let prodFn ← mkLambdaFVars #[] (mkApp diagExpr (mkBVar 0))
  -- Hmm, this is getting complicated. Let me use mkAppM more carefully.

  -- ∏ i, M.diag i   is   @Finset.prod (Fin n) ℤ _ Finset.univ (fun i => M.diag i)
  let diagFun ← withLocalDeclD `i finN fun i => do
    let di ← mkAppM ``Matrix.diag #[finalM]
    let dii := mkApp di i
    mkLambdaFVars #[i] dii
  let prodExpr ← mkAppM ``Finset.prod #[mkConst ``Finset.univ [.zero], diagFun]
  let prodEqProp ← mkEq prodExpr finalKExpr
  let prodProof ← mkDecide prodEqProp

  -- Apply det_upperTriangular_eq
  let mut proof ← mkAppM ``DetSimproc.det_upperTriangular_eq #[blockTriProof, prodProof]

  -- Step 3: Wrap each operation, working backwards
  for idx in [:ops.size] do
    let revIdx := ops.size - 1 - idx
    let op := ops[revIdx]!
    let k := kValues[revIdx]!
    let kExpr := mkIntLit k
    match op with
    | .combine i j a b => do
      let fi ← mkFinExpr n i
      let fj ← mkFinExpr n j
      let aExpr := mkIntLit a
      let bExpr := mkIntLit b
      -- Need proofs: i ≠ j and a ≠ 0
      let neqProp ← mkAppM ``Ne #[fi, fj]
      let neqProof ← mkDecide neqProp
      let aNeqProp ← mkAppM ``Ne #[aExpr, mkIntLit 0]
      let aNeqProof ← mkDecide aNeqProp
      -- Apply det_rowCombine
      -- det_rowCombine i j a b h hij ha
      proof ← mkAppM ``DetSimproc.det_rowCombine #[fi, fj, aExpr, bExpr, proof, neqProof, aNeqProof]
    | .swap i j => do
      let fi ← mkFinExpr n i
      let fj ← mkFinExpr n j
      let neqProp ← mkAppM ``Ne #[fi, fj]
      let neqProof ← mkDecide neqProp
      proof ← mkAppM ``DetSimproc.det_rowSwap #[fi, fj, proof, neqProof]

  return proof

end DetSimproc
