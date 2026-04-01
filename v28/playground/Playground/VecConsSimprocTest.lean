import Playground.VecConsSimproc
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
