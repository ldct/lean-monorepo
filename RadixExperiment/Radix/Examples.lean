/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # Radix Examples

Executable programs demonstrating the DSL syntax and fuel-based interpreter.
Each example uses `#eval!` to run the program and display the result.
-/

namespace Radix

/-- Display a Radix value in readable format. -/
def Value.display : Value → String
  | .uint64 n => toString n
  | .bool b   => toString b
  | .unit     => "()"
  | .str s    => s!"\"{s}\""
  | .addr a   => s!"<addr {a}>"

end Radix

namespace Radix.Examples

/-- Run a statement and display the value of variable `x`. -/
private def run (s : Stmt) (x : String) : String :=
  match s.run with
  | .ok σ => match σ.getVar x with
    | some v => v.display
    | none => s!"variable '{x}' not found"
  | .error msg => s!"error: {msg}"

/-- Run a program and display the value of variable `x`. -/
private def runProg (p : Program) (x : String) : String :=
  match p.run with
  | .ok σ => match σ.getVar x with
    | some v => v.display
    | none => s!"variable '{x}' not found"
  | .error msg => s!"error: {msg}"

/-! ## Factorial (iterative) -/

def factorial := `[RStmt|
  n := 12;
  result := 1;
  while (n > 0) {
    result := result * n;
    n := n - 1;
  }
]

#eval! run factorial "result"
-- 479001600

/-! ## Fibonacci -/

def fibonacci := `[RStmt|
  a := 0;
  b := 1;
  i := 0;
  while (i < 20) {
    tmp := b;
    b := a + b;
    a := tmp;
    i := i + 1;
  }
]

#eval! run fibonacci "a"
-- 6765

/-! ## Collatz Conjecture

Starting at 27, count steps to reach 1. -/

def collatz := `[RStmt|
  n := 27;
  steps := 0;
  while (n != 1) {
    if (n % 2 == 0) {
      n := n / 2;
    } else {
      n := n * 3 + 1;
    }
    steps := steps + 1;
  }
]

#eval! run collatz "steps"
-- 111

/-! ## FizzBuzz -/

def fizzbuzz := `[RStmt|
  result := "";
  i := 1;
  while (i <= 15) {
    if (i % 15 == 0) {
      result := result ++ "FizzBuzz ";
    } else {
      if (i % 3 == 0) {
        result := result ++ "Fizz ";
      } else {
        if (i % 5 == 0) {
          result := result ++ "Buzz ";
        } else {
          result := result ++ ". ";
        }
      }
    }
    i := i + 1;
  }
]

#eval! run fizzbuzz "result"

/-! ## Array: Sum of Squares

Allocate an array, fill with 1²..10², compute the sum. -/

def sumOfSquares := `[RStmt|
  let arr := new uint64[][10];
  i := 0;
  while (i < 10) {
    arr[i] := (i + 1) * (i + 1);
    i := i + 1;
  }
  sum := 0;
  i := 0;
  while (i < 10) {
    sum := sum + arr[i];
    i := i + 1;
  }
  free(arr);
]

#eval! run sumOfSquares "sum"
-- 385

/-! ## Bubble Sort

Sort [5, 3, 8, 1, 9, 2, 7, 4, 6, 0] in-place on a heap-allocated array. -/

def bubbleSort := `[RStmt|
  let arr := new uint64[][10];
  arr[0] := 5;
  arr[1] := 3;
  arr[2] := 8;
  arr[3] := 1;
  arr[4] := 9;
  arr[5] := 2;
  arr[6] := 7;
  arr[7] := 4;
  arr[8] := 6;
  arr[9] := 0;
  i := 0;
  while (i < 9) {
    j := 0;
    while (j < 9 - i) {
      let a : uint64 = arr[j];
      let b : uint64 = arr[j + 1];
      if (a > b) {
        arr[j] := b;
        arr[j + 1] := a;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  first := arr[0];
  last := arr[9];
]

#eval! run bubbleSort "first"  -- 0
#eval! run bubbleSort "last"   -- 9

/-! ## Function Call: Zero an Array

Demonstrates heap communication between caller and callee.
The function `zeroOut` receives an array address and zeros its elements
through the shared heap. -/

def zeroArray : Program := {
  funs := [
    { name := "zeroOut"
      params := [("a", .array .uint64), ("n", .uint64)]
      retTy := .unit
      body := `[RStmt|
        i := 0;
        while (i < n) {
          a[i] := 0;
          i := i + 1;
        }
      ]
    }
  ]
  main := `[RStmt|
    let arr := new uint64[][3];
    arr[0] := 10;
    arr[1] := 20;
    arr[2] := 30;
    zeroOut(arr, 3);
    val := arr[0];
  ]
}

#eval! runProg zeroArray "val"
-- 0 (was 10 before the function call)

end Radix.Examples
