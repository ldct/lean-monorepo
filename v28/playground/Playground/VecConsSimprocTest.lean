import Playground.VecConsSimproc
import Mathlib.LinearAlgebra.Matrix.Notation
import Qq

open Lean Qq Meta

/-- info: pass: non-vector returns none -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(ℕ) := q(42)
  guard (matchVecLit e == none)
  IO.println "pass: non-vector returns none"

/-- info: pass: vecEmpty returns [] -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Fin 0 → ℕ) := q(![])  
  let some xs := matchVecLit e | throwError "expected some"
  guard (xs.length == 0)
  IO.println "pass: vecEmpty returns []"

/-- info: pass: singleton returns 1 element -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Fin 1 → ℕ) := q(![7])
  let some xs := matchVecLit e | throwError "expected some"
  guard (xs.length == 1)
  IO.println "pass: singleton returns 1 element"

/-- info: pass: 3-element vector returns elements in order -/
#guard_msgs in
#eval show MetaM Unit from do
  let a : Q(ℕ) := q(10)
  let b : Q(ℕ) := q(20)
  let c : Q(ℕ) := q(30)
  let e : Q(Fin 3 → ℕ) := q(![$a, $b, $c])
  let some xs := matchVecLit e | throwError "expected some"
  guard (xs.length == 3)
  guard (xs[0]!.nat? == some 10)
  guard (xs[1]!.nat? == some 20)
  guard (xs[2]!.nat? == some 30)
  IO.println "pass: 3-element vector returns elements in order"

/-- info: pass: symbolic entries preserved -/
#guard_msgs in
#eval show MetaM Unit from do
  withLocalDecl `a .default q(ℕ) fun (a : Q(ℕ)) =>
  withLocalDecl `b .default q(ℕ) fun (b : Q(ℕ)) => do
    let e : Q(Fin 2 → ℕ) := q(![$a, $b])
    let some xs := matchVecLit e | throwError "expected some"
    guard (xs.length == 2)
    guard (xs[0]! == a)
    guard (xs[1]! == b)
    IO.println "pass: symbolic entries preserved"

/-- info: pass: non-literal tail returns none -/
#guard_msgs in
#eval show MetaM Unit from do
  withLocalDecl `f .default q(Fin 2 → ℕ) fun (f : Q(Fin 2 → ℕ)) => do
    let e : Q(Fin 3 → ℕ) := q(Matrix.vecCons (1 : ℕ) $f)
    guard (matchVecLit e == none)
    IO.println "pass: non-literal tail returns none"

-- ========== matchMatLitToVec tests ==========

/-- info: pass: non-matrix returns none -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(ℤ) := q(42)
  guard (matchMatLitToVec e == none)
  IO.println "pass: non-matrix returns none"

/-- info: pass: 1x1 matrix -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Matrix (Fin 1) (Fin 1) ℤ) := q(!![(5 : ℤ)])
  let some rows := matchMatLitToVec e | throwError "expected some"
  guard (rows.length == 1)
  guard (rows[0]!.length == 1)
  IO.println "pass: 1x1 matrix"

/-- info: pass: 2x2 matrix shape -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Matrix (Fin 2) (Fin 2) ℤ) := q(!![1, 2; 3, 4])
  let some rows := matchMatLitToVec e | throwError "expected some"
  guard (rows.length == 2)
  guard (rows[0]!.length == 2)
  guard (rows[1]!.length == 2)
  IO.println "pass: 2x2 matrix shape"

/-- info: pass: 2x2 matrix values -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Matrix (Fin 2) (Fin 2) ℤ) := q(!![1, 2; 3, 4])
  let some rows := matchMatLitToVec e | throwError "expected some"
  guard ((rows[0]!)[0]!.int? == some 1)
  guard ((rows[0]!)[1]!.int? == some 2)
  guard ((rows[1]!)[0]!.int? == some 3)
  guard ((rows[1]!)[1]!.int? == some 4)
  IO.println "pass: 2x2 matrix values"

/-- info: pass: 2x3 rectangular matrix -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Matrix (Fin 2) (Fin 3) ℤ) := q(!![1, 2, 3; 4, 5, 6])
  let some rows := matchMatLitToVec e | throwError "expected some"
  guard (rows.length == 2)
  guard (rows[0]!.length == 3)
  guard (rows[1]!.length == 3)
  guard ((rows[0]!)[0]!.int? == some 1)
  guard ((rows[0]!)[2]!.int? == some 3)
  guard ((rows[1]!)[0]!.int? == some 4)
  guard ((rows[1]!)[2]!.int? == some 6)
  IO.println "pass: 2x3 rectangular matrix"

/-- info: pass: 3x3 matrix with negatives -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Matrix (Fin 3) (Fin 3) ℤ) := q(!![(1 : ℤ), -2, 3; -4, 5, -6; 7, -8, 9])
  let some rows := matchMatLitToVec e | throwError "expected some"
  guard (rows.length == 3)
  for row in rows do
    guard (row.length == 3)
  guard ((rows[1]!)[0]!.int? == some (-4))
  guard ((rows[2]!)[1]!.int? == some (-8))
  IO.println "pass: 3x3 matrix with negatives"

/-- info: pass: plain vector is not a matrix -/
#guard_msgs in
#eval show MetaM Unit from do
  let e : Q(Fin 3 → ℤ) := q(![1, 2, 3])
  guard (matchMatLitToVec e == none)
  IO.println "pass: plain vector is not a matrix"

-- ========== updateRowSimproc tests ==========

example : Matrix.updateRow !![1, 2, 3; 4, 5, 6; 7, 8, 9] (1 : Fin 3) ![10, 20, 30]
    = !![1, 2, 3; 10, 20, 30; 7, 8, 9] := by
  simp only [updateRowSimproc]

example : Matrix.updateRow !![(1:ℤ), 2; 3, 4] (0 : Fin 2) ![(-1:ℤ), -2]
    = !![(-1:ℤ), -2; 3, 4] := by
  simp only [updateRowSimproc]

example : Matrix.updateRow !![(1:ℤ), 2; 3, 4] (1 : Fin 2) ![(-1:ℤ), -2]
    = !![(1:ℤ), 2; -1, -2] := by
  simp only [updateRowSimproc]

-- 1x1 matrix
example : Matrix.updateRow !![(5:ℤ)] (0 : Fin 1) ![(7:ℤ)]
    = !![(7:ℤ)] := by
  simp only [updateRowSimproc]

-- last row of a 3x3
example : Matrix.updateRow !![1, 2, 3; 4, 5, 6; 7, 8, 9] (2 : Fin 3) ![0, 0, 0]
    = !![1, 2, 3; 4, 5, 6; 0, 0, 0] := by
  simp only [updateRowSimproc]

-- with `show` coercion (the letE wrapper case)
example : (show Matrix (Fin 2) (Fin 2) ℤ from !![1, 2; 3, 4]).updateRow 0 ![10, 20]
    = !![10, 20; 3, 4] := by
  simp only [updateRowSimproc]
