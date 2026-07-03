/-!
# Pure-Lean Gaussian elimination over ℤ

Given an `n × n` integer matrix (as `Array (Array Int)`), performs Gaussian
elimination and returns the sequence of row operations and the final
upper-triangular matrix.
-/

namespace DetSimproc

/-- A row operation recorded during elimination. -/
inductive RowOp where
  /-- Replace row `i` with `a • row[i] + b • row[j]`.
      The scale factor on the determinant is `a`. -/
  | combine (i j : Nat) (a b : Int)
  /-- Swap rows `i` and `j`. -/
  | swap (i j : Nat)
  deriving Repr

/-- State during Gaussian elimination. -/
structure GaussState where
  matrix : Array (Array Int)
  ops : Array RowOp
  /-- Accumulated scale factor: det(original) * scaleFactor = det(current) -/
  scaleFactor : Int
  deriving Repr

def GaussState.n (s : GaussState) : Nat := s.matrix.size

/-- Get entry `(i, j)` from the state's matrix. -/
def GaussState.get (s : GaussState) (i j : Nat) : Int :=
  (s.matrix.getD i #[]).getD j 0

/-- Update a row in the state's matrix. -/
def GaussState.updateRow (s : GaussState) (i : Nat) (newRow : Array Int) : GaussState :=
  { s with matrix := s.matrix.set! i newRow }

/-- Apply row operation: row[i] ← a * row[i] + b * row[j] -/
def applyRowCombine (m : Array (Array Int)) (i j : Nat) (a b : Int) : Array (Array Int) :=
  let ri := m.getD i #[]
  let rj := m.getD j #[]
  let newRow := Array.zipWith (fun x y => a * x + b * y) ri rj
  m.set! i newRow

/-- Swap rows i and j. -/
def applyRowSwap (m : Array (Array Int)) (i j : Nat) : Array (Array Int) :=
  let ri := m.getD i #[]
  let rj := m.getD j #[]
  (m.set! i rj).set! j ri

/-- Find the best pivot row in column `col` among rows `col..n-1`.
    Returns the row index with smallest nonzero absolute value, or `none`. -/
def findPivot (m : Array (Array Int)) (col : Nat) : Option Nat := Id.run do
  let n := m.size
  let mut best : Option (Nat × Int) := none
  for r in [col:n] do
    let v := (m.getD r #[]).getD col 0
    if v != 0 then
      match best with
      | none => best := some (r, v.natAbs)
      | some (_, bestAbs) =>
        if v.natAbs < bestAbs then
          best := some (r, v.natAbs)
  return best.map Prod.fst

/-- Run Gaussian elimination on an integer matrix.
    Returns the sequence of row operations and the final upper-triangular matrix. -/
def gaussElim (matrix : Array (Array Int)) : GaussState := Id.run do
  let n := matrix.size
  let mut state : GaussState := {
    matrix := matrix
    ops := #[]
    scaleFactor := 1
  }
  for col in [:n] do
    -- Find pivot
    match findPivot state.matrix col with
    | none => continue  -- entire column is zero
    | some pivotRow =>
      -- Swap if needed
      if pivotRow != col then
        state := {
          matrix := applyRowSwap state.matrix col pivotRow
          ops := state.ops.push (.swap col pivotRow)
          scaleFactor := state.scaleFactor
        }
      -- Eliminate below
      let pivot := state.get col col
      for r in [col + 1 : n] do
        let entry := state.get r col
        if entry != 0 then
          -- row[r] ← pivot * row[r] - entry * row[col]
          -- This zeros out position (r, col)
          -- The determinant scales by `pivot`
          let g := Int.gcd pivot entry
          let a := pivot / g
          let b := -entry / g
          state := {
            matrix := applyRowCombine state.matrix r col a b
            ops := state.ops.push (.combine r col a b)
            scaleFactor := state.scaleFactor * a
          }
  return state

/-- Compute the determinant from the final state.
    det(original) = product(diagonal) / scaleFactor -/
def computeDet (state : GaussState) : Int := Id.run do
  let n := state.matrix.size
  let mut diagProd : Int := 1
  for i in [:n] do
    diagProd := diagProd * state.get i i
  -- Account for swaps (each swap negates det)
  let numSwaps := state.ops.foldl (fun acc op =>
    match op with | .swap _ _ => acc + 1 | _ => acc) 0
  let sign : Int := if numSwaps % 2 == 0 then 1 else -1
  return sign * diagProd / state.scaleFactor

end DetSimproc
