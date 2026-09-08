/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # Basic Tests

Arithmetic, variables, control flow.
-/

namespace Radix.Tests

private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

-- Simple assignment and arithmetic
def test_assign := `[RStmt|
  x := 3;
  y := 5;
  z := x + y;
]

#guard getResult test_assign "z" == some (Value.uint64 8)

-- If-then-else
def test_ite := `[RStmt|
  x := 10;
  if (x < 20) {
    y := 1;
  } else {
    y := 0;
  }
]

#guard getResult test_ite "y" == some (Value.uint64 1)

-- While loop: compute 1 + 2 + ... + 10
def test_while := `[RStmt|
  sum := 0;
  i := 1;
  while (i <= 10) {
    sum := sum + i;
    i := i + 1;
  }
]

#guard getResult test_while "sum" == some (Value.uint64 55)

-- Nested if
def test_nested_if := `[RStmt|
  x := 5;
  if (x > 3) {
    if (x < 10) {
      y := 1;
    } else {
      y := 2;
    }
  } else {
    y := 3;
  }
]

#guard getResult test_nested_if "y" == some (Value.uint64 1)

-- Boolean operations
def test_bool := `[RStmt|
  a := true;
  b := false;
  c := a && b;
  d := a || b;
  e := !b;
]

#guard getResult test_bool "c" == some (Value.bool false)
#guard getResult test_bool "d" == some (Value.bool true)
#guard getResult test_bool "e" == some (Value.bool true)

-- Multiplication and modulo
def test_arith := `[RStmt|
  x := 7;
  y := 3;
  prod := x * y;
  rem := x % y;
]

#guard getResult test_arith "prod" == some (Value.uint64 21)
#guard getResult test_arith "rem" == some (Value.uint64 1)

-- Countdown loop
def test_countdown := `[RStmt|
  n := 10;
  while (n > 0) {
    n := n - 1;
  }
]

#guard getResult test_countdown "n" == some (Value.uint64 0)

-- Equality and inequality
def test_comparison := `[RStmt|
  x := 5;
  y := 5;
  eq := x == y;
  ne := x != y;
]

#guard getResult test_comparison "eq" == some (Value.bool true)
#guard getResult test_comparison "ne" == some (Value.bool false)

/-! ## Edge cases -/

-- Division
def test_division := `[RStmt|
  x := 10;
  y := 3;
  q := x / y;
  r := x % y;
]

#guard getResult test_division "q" == some (Value.uint64 3)
#guard getResult test_division "r" == some (Value.uint64 1)

-- Division by zero produces error (expr eval returns none → interp fails)
def test_div_by_zero := `[RStmt|
  x := 10;
  y := 0;
  q := x / y;
]

#guard (test_div_by_zero.run).isOk == false

-- Mod by zero also errors
def test_mod_by_zero := `[RStmt|
  x := 10;
  y := 0;
  q := x % y;
]

#guard (test_mod_by_zero.run).isOk == false

-- Subtraction underflow (UInt64 wraps around)
def test_sub_underflow := `[RStmt|
  x := 3;
  y := 5;
  z := x - y;
]

-- UInt64 subtraction wraps: 3 - 5 = UInt64.max - 1
#guard (getResult test_sub_underflow "z").isSome

-- Greater-than-or-equal
def test_ge := `[RStmt|
  x := 5;
  y := 5;
  a := x >= y;
  z := x >= 3;
]

#guard getResult test_ge "a" == some (Value.bool true)
#guard getResult test_ge "z" == some (Value.bool true)

-- Nested blocks
def test_nested_block :=
  Stmt.block [
    Stmt.assign "x" (Expr.lit (Value.uint64 1)),
    Stmt.block [
      Stmt.assign "y" (Expr.lit (Value.uint64 2)),
      Stmt.block [
        Stmt.assign "z" (Expr.binop .add (Expr.var "x") (Expr.var "y"))
      ]
    ]
  ]

#guard getResult test_nested_block "z" == some (Value.uint64 3)

-- Deeply nested while (while inside while)
def test_nested_while := `[RStmt|
  total := 0;
  i := 0;
  while (i < 3) {
    j := 0;
    while (j < 3) {
      total := total + 1;
      j := j + 1;
    }
    i := i + 1;
  }
]

#guard getResult test_nested_while "total" == some (Value.uint64 9)

-- If without else (else branch is skip)
def test_if_no_else := `[RStmt|
  x := 10;
  y := 0;
  if (x > 5) {
    y := 1;
  }
]

#guard getResult test_if_no_else "y" == some (Value.uint64 1)

-- If with false condition and no else
def test_if_false_no_else := `[RStmt|
  x := 1;
  y := 0;
  if (x > 5) {
    y := 1;
  }
]

#guard getResult test_if_false_no_else "y" == some (Value.uint64 0)

-- While loop that never executes
def test_while_false := `[RStmt|
  x := 0;
  while (false) {
    x := 1;
  }
]

#guard getResult test_while_false "x" == some (Value.uint64 0)

-- Negation (unary)
def test_neg :=
  let assign := Stmt.assign "x" (Expr.lit (Value.uint64 5))
  let neg := Stmt.assign "y" (Expr.unop .neg (Expr.var "x"))
  assign ;; neg

-- neg wraps: 0 - 5 in UInt64
#guard (getResult test_neg "y").isSome

-- Out-of-fuel error
def test_out_of_fuel := `[RStmt|
  x := 0;
  while (true) {
    x := x + 1;
  }
]

#guard (test_out_of_fuel.run (fuel := 100)).isOk == false

/-! ## Scope tests -/

-- Scope isolates variables: inner scope gets its own frame
def test_scope_basic :=
  let outer := Stmt.assign "x" (Expr.lit (Value.uint64 10))
  let scopeBody := Stmt.assign "y" (Expr.binop .add (Expr.var "a") (Expr.lit (Value.uint64 1)))
  let inner := Stmt.scope [("a", Ty.uint64)] [Expr.var "x"] scopeBody
  outer ;; inner

-- x should still be visible after scope, but variables created inside scope (y) should not leak
#guard getResult test_scope_basic "x" == some (Value.uint64 10)
-- y was assigned inside the scope's frame, so it should not be visible in the outer frame
#guard getResult test_scope_basic "y" == none

-- Scope with multiple parameters
def test_scope_multi_params :=
  let init_a := Stmt.assign "a" (Expr.lit (Value.uint64 3))
  let init_b := Stmt.assign "b" (Expr.lit (Value.uint64 7))
  let scopeBody := Stmt.assign "result" (Expr.binop .add (Expr.var "p") (Expr.var "q"))
  let inner := Stmt.scope [("p", Ty.uint64), ("q", Ty.uint64)]
    [Expr.var "a", Expr.var "b"] scopeBody
  -- After scope, "result" should not leak out
  init_a ;; init_b ;; inner

#guard getResult test_scope_multi_params "a" == some (Value.uint64 3)
#guard getResult test_scope_multi_params "b" == some (Value.uint64 7)
#guard getResult test_scope_multi_params "result" == none

-- Nested scopes: each scope gets its own frame
def test_scope_nested :=
  let outer_assign := Stmt.assign "x" (Expr.lit (Value.uint64 5))
  let inner_scope := Stmt.scope [("y", Ty.uint64)] [Expr.lit (Value.uint64 10)]
    (Stmt.assign "z" (Expr.var "y"))
  let outer_scope := Stmt.scope [("a", Ty.uint64)] [Expr.var "x"]
    (Stmt.seq (Stmt.assign "b" (Expr.var "a")) inner_scope)
  outer_assign ;; outer_scope

-- x survives, but a, b, y, z are in scope frames and don't leak
#guard getResult test_scope_nested "x" == some (Value.uint64 5)
#guard getResult test_scope_nested "a" == none
#guard getResult test_scope_nested "b" == none
#guard getResult test_scope_nested "z" == none

/-! ## Return semantics -/

-- Return from within a function
def test_return_from_func : Program := {
  funs := [
    { name := "earlyReturn"
      params := [("n", .uint64)]
      retTy := .uint64
      body := `[RStmt|
        if (n < 5) {
          return 0;
        }
        return 1;
      ] }
  ]
  main := `[RStmt|
    earlyReturn(3);
  ]
}

#guard (test_return_from_func.run 10000).isOk

-- Return from within a while loop in a function
def test_return_from_while : Program := {
  funs := [
    { name := "findFirst"
      params := [("target", .uint64)]
      retTy := .uint64
      body := `[RStmt|
        i := 0;
        while (i < 100) {
          if (i == target) {
            return i;
          }
          i := i + 1;
        }
        return 0;
      ] }
  ]
  main := `[RStmt|
    findFirst(7);
  ]
}

#guard (test_return_from_while.run 10000).isOk

-- Return short-circuits sequence: code after return is not executed
def test_return_shortcircuit : Program := {
  funs := [
    { name := "f"
      params := List.nil
      retTy := .uint64
      body := `[RStmt|
        x := 1;
        return 42;
        x := 999;
      ] }
  ]
  main := `[RStmt|
    f();
  ]
}

#guard (test_return_shortcircuit.run 10000).isOk

/-! ## Error cases -/

-- Undefined variable
def test_undef_var := `[RStmt|
  y := x + 1;
]

#guard (test_undef_var.run).isOk == false

-- If condition is not a bool
def test_if_non_bool :=
  let assign := Stmt.assign "x" (Expr.lit (Value.uint64 5))
  let bad_if := Stmt.ite (Expr.var "x") Stmt.skip Stmt.skip
  assign ;; bad_if

#guard (test_if_non_bool.run).isOk == false

-- While condition is not a bool
def test_while_non_bool :=
  let assign := Stmt.assign "x" (Expr.lit (Value.uint64 5))
  let bad_while := Stmt.while (Expr.var "x") Stmt.skip
  assign ;; bad_while

#guard (test_while_non_bool.run).isOk == false

end Radix.Tests
