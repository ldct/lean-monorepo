/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # String Tests

String operations: concatenation, length, indexing.
-/

namespace Radix.Tests

private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

-- String concatenation
def test_str_append := `[RStmt|
  s1 := "hello";
  s2 := " world";
  s3 := s1 ++ s2;
]

#guard getResult test_str_append "s3" == some (Value.str "hello world")

-- String length (manual AST since strLen is not in syntax)
def test_str_len :=
  let assign := Stmt.assign "s" (Expr.lit (Value.str "hello"))
  let len := Stmt.assign "n" (Expr.strLen (Expr.var "s"))
  assign ;; len

#guard getResult test_str_len "n" == some (Value.uint64 5)

-- String reversal program
def strReverseProgram : Program := {
  funs := [
    { name := "strReverse"
      params := [("s", Ty.string)]
      retTy := Ty.string
      body :=
        let getLen := Stmt.assign "len" (Expr.strLen (Expr.var "s"))
        let init := Stmt.assign "result" (Expr.lit (Value.str ""))
        let loop := `[RStmt|
          i := 0;
          while (i < len) {
            i := i + 1;
          }
        ]
        getLen ;; init ;; loop }
  ]
  main := `[RStmt|
    strReverse("hello");
  ]
}

#guard (strReverseProgram.run 10000).isOk

-- Empty string
def test_empty_str := `[RStmt|
  s := "";
]

#guard getResult test_empty_str "s" == some (Value.str "")

-- String length of empty string
def test_str_len_empty :=
  let assign := Stmt.assign "s" (Expr.lit (Value.str ""))
  let len := Stmt.assign "n" (Expr.strLen (Expr.var "s"))
  assign ;; len

#guard getResult test_str_len_empty "n" == some (Value.uint64 0)

-- String indexing (strGet) basic
def test_str_get :=
  let assign := Stmt.assign "s" (Expr.lit (Value.str "abcde"))
  let get0 := Stmt.assign "c0" (Expr.strGet (Expr.var "s") (Expr.lit (Value.uint64 0)))
  let get2 := Stmt.assign "c2" (Expr.strGet (Expr.var "s") (Expr.lit (Value.uint64 2)))
  let get4 := Stmt.assign "c4" (Expr.strGet (Expr.var "s") (Expr.lit (Value.uint64 4)))
  assign ;; get0 ;; get2 ;; get4

#guard getResult test_str_get "c0" == some (Value.str "a")
#guard getResult test_str_get "c2" == some (Value.str "c")
#guard getResult test_str_get "c4" == some (Value.str "e")

-- String indexing out of bounds
def test_str_get_oob :=
  let assign := Stmt.assign "s" (Expr.lit (Value.str "hi"))
  let get := Stmt.assign "c" (Expr.strGet (Expr.var "s") (Expr.lit (Value.uint64 5)))
  assign ;; get

-- Out-of-bounds strGet returns none in Expr.eval, causing interp to error
#guard (test_str_get_oob.run).isOk == false

-- String indexing on empty string
def test_str_get_empty :=
  let assign := Stmt.assign "s" (Expr.lit (Value.str ""))
  let get := Stmt.assign "c" (Expr.strGet (Expr.var "s") (Expr.lit (Value.uint64 0)))
  assign ;; get

#guard (test_str_get_empty.run).isOk == false

-- String length after concatenation
def test_str_len_concat :=
  let s1 := Stmt.assign "a" (Expr.lit (Value.str "hello"))
  let s2 := Stmt.assign "b" (Expr.lit (Value.str " world"))
  let cat := Stmt.assign "c" (Expr.binop .strAppend (Expr.var "a") (Expr.var "b"))
  let len := Stmt.assign "n" (Expr.strLen (Expr.var "c"))
  s1 ;; s2 ;; cat ;; len

#guard getResult test_str_len_concat "n" == some (Value.uint64 11)

-- Repeated concatenation
def test_str_repeat_concat := `[RStmt|
  s := "";
  i := 0;
  while (i < 3) {
    s := s ++ "ab";
    i := i + 1;
  }
]

#guard getResult test_str_repeat_concat "s" == some (Value.str "ababab")

-- String length in a loop
def test_str_len_loop :=
  let init_s := Stmt.assign "s" (Expr.lit (Value.str "hello"))
  let init_len := Stmt.assign "n" (Expr.strLen (Expr.var "s"))
  -- n should be 5
  init_s ;; init_len

#guard getResult test_str_len_loop "n" == some (Value.uint64 5)

-- String equality
def test_str_eq := `[RStmt|
  a := "hello";
  b := "hello";
  c := "world";
  eq1 := a == b;
  eq2 := a == c;
  ne1 := a != c;
]

#guard getResult test_str_eq "eq1" == some (Value.bool true)
#guard getResult test_str_eq "eq2" == some (Value.bool false)
#guard getResult test_str_eq "ne1" == some (Value.bool true)

-- strLen on non-string value should error
def test_strlen_wrong_type :=
  let assign := Stmt.assign "x" (Expr.lit (Value.uint64 42))
  let len := Stmt.assign "n" (Expr.strLen (Expr.var "x"))
  assign ;; len

#guard (test_strlen_wrong_type.run).isOk == false

end Radix.Tests
