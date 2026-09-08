/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # Array Tests

Allocation, indexing, modification, free.
-/

namespace Radix.Tests

-- Allocate, write, read
def test_array_basic :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 5))
  let set0 := Stmt.arrSet (Expr.var "arr") (Expr.lit (Value.uint64 0)) (Expr.lit (Value.uint64 42))
  let set1 := Stmt.arrSet (Expr.var "arr") (Expr.lit (Value.uint64 1)) (Expr.lit (Value.uint64 99))
  let read := Stmt.assign "val" (Expr.arrGet (Expr.var "arr") (Expr.lit (Value.uint64 0)))
  let free := Stmt.free (Expr.var "arr")
  alloc ;; set0 ;; set1 ;; read ;; free

private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

#guard getResult test_array_basic "val" == some (Value.uint64 42)

-- Array sum using manual AST (since RExpr doesn't support arr[i] reads)
def arraySumProgram : Program := {
  funs := [
    { name := "arraySum"
      params := [("n", Ty.uint64)]
      retTy := Ty.uint64
      body :=
        let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.var "n")
        let fill := `[RStmt|
          i := 0;
          while (i < n) {
            arr[i] := i + 1;
            i := i + 1;
          }
        ]
        let sumLoop :=
          let init1 := Stmt.assign "total" (Expr.lit (Value.uint64 0))
          let init2 := Stmt.assign "j" (Expr.lit (Value.uint64 0))
          let readJ := Stmt.assign "elem" (Expr.arrGet (Expr.var "arr") (Expr.var "j"))
          let addElem := Stmt.assign "total" (Expr.binop BinOp.add (Expr.var "total") (Expr.var "elem"))
          let incJ := Stmt.assign "j" (Expr.binop BinOp.add (Expr.var "j") (Expr.lit (Value.uint64 1)))
          let body := readJ ;; addElem ;; incJ
          let cond := Expr.binop BinOp.lt (Expr.var "j") (Expr.var "n")
          init1 ;; init2 ;; Stmt.while cond body
        let free := Stmt.free (Expr.var "arr")
        alloc ;; fill ;; sumLoop ;; free }
  ]
  main := `[RStmt| arraySum(10); ]
}

#guard (arraySumProgram.run 10000).isOk

-- Bubble sort (simplified — just tests alloc/fill/free cycle)
def bubbleSortProgram : Program := {
  funs := [
    { name := "bubbleSort"
      params := [("n", Ty.uint64)]
      retTy := Ty.unit
      body :=
        let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.var "n")
        let fill := `[RStmt|
          k := 0;
          while (k < n) {
            arr[k] := n - k;
            k := k + 1;
          }
        ]
        let free := Stmt.free (Expr.var "arr")
        alloc ;; fill ;; free }
  ]
  main := `[RStmt| bubbleSort(5); ]
}

#guard (bubbleSortProgram.run 10000).isOk

/-! ## Array edge cases -/

-- Zero-length allocation
def test_zero_alloc :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 0))
  let len := Stmt.assign "n" (Expr.arrLen (Expr.var "arr"))
  let free := Stmt.free (Expr.var "arr")
  alloc ;; len ;; free

#guard getResult test_zero_alloc "n" == some (Value.uint64 0)

-- Array length query
def test_array_len :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 7))
  let len := Stmt.assign "n" (Expr.arrLen (Expr.var "arr"))
  let free := Stmt.free (Expr.var "arr")
  alloc ;; len ;; free

#guard getResult test_array_len "n" == some (Value.uint64 7)

-- Out-of-bounds read produces error
def test_oob_read :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 3))
  let read := Stmt.assign "val" (Expr.arrGet (Expr.var "arr") (Expr.lit (Value.uint64 5)))
  alloc ;; read

#guard (test_oob_read.run).isOk == false

-- Out-of-bounds write produces error
def test_oob_write :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 3))
  let write := Stmt.arrSet (Expr.var "arr") (Expr.lit (Value.uint64 10)) (Expr.lit (Value.uint64 42))
  alloc ;; write

#guard (test_oob_write.run).isOk == false

-- Read at valid boundary (last element)
def test_boundary_read :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 3))
  let set := Stmt.arrSet (Expr.var "arr") (Expr.lit (Value.uint64 2)) (Expr.lit (Value.uint64 77))
  let read := Stmt.assign "val" (Expr.arrGet (Expr.var "arr") (Expr.lit (Value.uint64 2)))
  let free := Stmt.free (Expr.var "arr")
  alloc ;; set ;; read ;; free

#guard getResult test_boundary_read "val" == some (Value.uint64 77)

-- Free invalid address produces error
def test_free_invalid :=
  Stmt.free (Expr.lit (Value.addr 9999))

#guard (test_free_invalid.run).isOk == false

-- Double free produces error
def test_double_free :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 2))
  let free1 := Stmt.free (Expr.var "arr")
  let free2 := Stmt.free (Expr.var "arr")
  alloc ;; free1 ;; free2

#guard (test_double_free.run).isOk == false

-- Read after free produces error
def test_read_after_free :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 2))
  let set := Stmt.arrSet (Expr.var "arr") (Expr.lit (Value.uint64 0)) (Expr.lit (Value.uint64 42))
  let free := Stmt.free (Expr.var "arr")
  let read := Stmt.assign "val" (Expr.arrGet (Expr.var "arr") (Expr.lit (Value.uint64 0)))
  alloc ;; set ;; free ;; read

#guard (test_read_after_free.run).isOk == false

-- Multiple arrays can coexist
def test_multi_array :=
  let alloc1 := Stmt.alloc "a" Ty.uint64 (Expr.lit (Value.uint64 2))
  let alloc2 := Stmt.alloc "b" Ty.uint64 (Expr.lit (Value.uint64 3))
  let set_a := Stmt.arrSet (Expr.var "a") (Expr.lit (Value.uint64 0)) (Expr.lit (Value.uint64 10))
  let set_b := Stmt.arrSet (Expr.var "b") (Expr.lit (Value.uint64 0)) (Expr.lit (Value.uint64 20))
  let read_a := Stmt.assign "va" (Expr.arrGet (Expr.var "a") (Expr.lit (Value.uint64 0)))
  let read_b := Stmt.assign "vb" (Expr.arrGet (Expr.var "b") (Expr.lit (Value.uint64 0)))
  let free_a := Stmt.free (Expr.var "a")
  let free_b := Stmt.free (Expr.var "b")
  alloc1 ;; alloc2 ;; set_a ;; set_b ;; read_a ;; read_b ;; free_a ;; free_b

#guard getResult test_multi_array "va" == some (Value.uint64 10)
#guard getResult test_multi_array "vb" == some (Value.uint64 20)

-- Newly allocated array is zero-initialized
def test_zero_init :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 3))
  let read := Stmt.assign "val" (Expr.arrGet (Expr.var "arr") (Expr.lit (Value.uint64 1)))
  let free := Stmt.free (Expr.var "arr")
  alloc ;; read ;; free

#guard getResult test_zero_init "val" == some (Value.uint64 0)

end Radix.Tests
