import Mathlib
import Playground.LUMinScaling

/-!
# `intDetSimproc` — determinants of integer matrices via scaled LU

Rewrites `Matrix.det A` to an integer literal for concrete
`A : Matrix (Fin n) (Fin n) ℤ`, by computing `exactMinScaling` on the
rational version and using `det(L_int * U_int) = n_min^n * det A`.
-/

namespace IntDetSimproc

open Lean Meta

/-- Cancel `k^n` from `det (k • M) = k^n * d` to get `det M = d`. -/
lemma det_of_smul_det {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ} {d : ℤ}
    (hk : k ≠ 0)
    (h : (k • M).det = k ^ n * d) :
    M.det = d := by
  rw [Matrix.det_smul, Fintype.card_fin] at h
  exact mul_left_cancel₀ (pow_ne_zero n hk) h

/-- Materialise an `n × n` integer matrix as a `List (List Int)` for
reflection. Used by `evalIntMatrixExpr`. -/
def toLists (n : Nat) (M : Matrix (Fin n) (Fin n) Int) : List (List Int) :=
  (List.finRange n).map fun i => (List.finRange n).map fun j => M i j

/-- Build a matrix from a `List (List Int)`; used to emit `L_int`, `U_int`
as kernel-computable Lean terms inside the simproc-generated proof. -/
def matOfList (n : Nat) (rows : List (List Int)) : Matrix (Fin n) (Fin n) Int :=
  Matrix.of fun i j => (rows.getD i.val []).getD j.val 0

/-- Packaged decidable witness for `A.det = d` via a scaled LU decomposition.

Given literal ingredients `A, L, U, k, d, detL, detU` the simproc produces a
term of this type via `decide +kernel` (through `mkDecideProof`), and then
applies `det_eq_of_witness` to get `A.det = d`. -/
abbrev intDetWitness {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℤ)
    (k d detL detU : ℤ) : Prop :=
  k ≠ 0 ∧
  k • A = L * U ∧
  (∀ i j : Fin n, i < j → L i j = 0) ∧
  (∀ i j : Fin n, j < i → U i j = 0) ∧
  (∏ i, L i i) = detL ∧
  (∏ i, U i i) = detU ∧
  detL * detU = k ^ n * d

lemma det_eq_of_witness {n : ℕ} {A L U : Matrix (Fin n) (Fin n) ℤ}
    {k d detL detU : ℤ}
    (h : intDetWitness A L U k d detL detU) : A.det = d := by
  obtain ⟨hk, hLU, hLtri, hUtri, hLprod, hUprod, harith⟩ := h
  have hLtri' : L.BlockTriangular OrderDual.toDual :=
    fun i j hij => hLtri i j hij
  have hUtri' : U.BlockTriangular id :=
    fun i j hij => hUtri i j hij
  have hLdet : L.det = detL :=
    (Matrix.det_of_lowerTriangular L hLtri').trans hLprod
  have hUdet : U.det = detU :=
    (Matrix.det_of_upperTriangular hUtri').trans hUprod
  apply det_of_smul_det hk
  rw [hLU, Matrix.det_mul, hLdet, hUdet, harith]

/-- Given `(idxTy, R, A)` extracted from a `Matrix.det` application,
return `(n, rows)` with the concrete integer entries, provided
`idxTy = Fin n` for a literal `n` and `R = Int`. -/
unsafe def evalIntMatrixExpr (idxTy R A : Expr) :
    MetaM (Option (Nat × List (List Int))) := do
  unless R.isConstOf ``Int do return none
  let_expr Fin nExpr := idxTy | return none
  let nVal ← try Lean.Meta.evalExpr Nat (mkConst ``Nat) nExpr catch _ => return none
  let listIntTy := mkApp (mkConst ``List [0]) (mkConst ``Int)
  let listListIntTy := mkApp (mkConst ``List [0]) listIntTy
  let call := mkApp2 (mkConst ``IntDetSimproc.toLists) (mkNatLit nVal) A
  let lists ← try Lean.Meta.evalExpr (List (List Int)) listListIntTy call
               catch _ => return none
  return some (nVal, lists)

/-- The main simproc: rewrites `Matrix.det A` to a concrete integer
literal for integer matrices whose rational LU decomposition exists
(pivotless) and is non-singular. -/
simproc_decl intDetSimproc (Matrix.det _) := fun e => do
  -- Args of `@Matrix.det`: {n} [DecidableEq n] [Fintype n] {R} [CommRing R] (M).
  let args := e.getAppArgs
  unless args.size ≥ 6 do return .continue
  let idxTy := args[0]!
  let R := args[3]!
  let A := args[5]!
  let some (n, rows) ← unsafe evalIntMatrixExpr idxTy R A | return .continue
  -- Degenerate sizes — defer to existing simp lemmas.
  if n = 0 then return .continue
  if n = 1 then return .continue
  -- Run exactMinScaling on the rational lift of `A`.
  let qmat : QMat := rows.map (·.map Rat.ofInt)
  let some data := exactMinScaling qmat | return .continue
  let rowsL : List (List Int) := (List.range n).map fun i =>
    (List.range n).map fun j => (data.L_int.get i j).num
  let rowsU : List (List Int) := (List.range n).map fun i =>
    (List.range n).map fun j => (data.U_int.get i j).num
  let detL : Int := (List.range n).foldl
    (fun acc i => acc * (rowsL.getD i []).getD i 0) 1
  let detU : Int := (List.range n).foldl
    (fun acc i => acc * (rowsU.getD i []).getD i 0) 1
  let nminPow : Int := (data.n_min : Int) ^ n
  if nminPow = 0 then return .continue
  let prod := detL * detU
  if prod % nminPow ≠ 0 then return .continue
  let d := prod / nminPow
  -- Build the witness and its `decide +kernel` proof.
  let nLit := mkNatLit n
  let LExpr := mkApp2 (mkConst ``IntDetSimproc.matOfList) nLit (Lean.toExpr rowsL)
  let UExpr := mkApp2 (mkConst ``IntDetSimproc.matOfList) nLit (Lean.toExpr rowsU)
  let kExpr := Lean.toExpr (data.n_min : Int)
  let dExpr := Lean.toExpr d
  let detLExpr := Lean.toExpr detL
  let detUExpr := Lean.toExpr detU
  let witnessProp := mkAppN (mkConst ``IntDetSimproc.intDetWitness)
    #[nLit, A, LExpr, UExpr, kExpr, dExpr, detLExpr, detUExpr]
  let witnessProof ← try mkDecideProof witnessProp
                     catch _ => return .continue
  let proof ← mkAppM ``IntDetSimproc.det_eq_of_witness #[witnessProof]
  return .done { expr := dExpr, proof? := some proof }

end IntDetSimproc
