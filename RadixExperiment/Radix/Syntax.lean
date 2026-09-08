/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Interp

/-! # Radix Concrete Syntax

Custom syntax categories for writing Radix programs naturally.

Two syntax quotations are provided:
- `` `[RExpr| ...] `` for expressions: arithmetic, comparisons, booleans,
  string append, array indexing (`arr[i]`), and variable references.
- `` `[RStmt| ...] `` for statements: assignment, `let` declarations,
  `let ... := new T[n]` allocation, `if/else`, `while`, `free(...)`,
  array write, function calls, and `return`.

Array length and string operations use helper macros `arrLen(...)`,
`strLen(...)`, `strGet(...)` that produce `Expr` values directly.
-/

namespace Radix

/-! ## Expression syntax -/

syntax "`[RExpr|" term "]" : term

macro_rules
  | `(`[RExpr| true])      => `(Expr.lit (.bool true))
  | `(`[RExpr| false])     => `(Expr.lit (.bool false))
  | `(`[RExpr| ()])        => `(Expr.lit .unit)
  | `(`[RExpr| $n:num])    => `(Expr.lit (.uint64 $n))
  | `(`[RExpr| $s:str])    => `(Expr.lit (.str $s))
  | `(`[RExpr| $x:ident])  => `(Expr.var $(Lean.quote x.getId.toString))
  | `(`[RExpr| ($x)])      => `(`[RExpr| $x])
  | `(`[RExpr| $x + $y])   => `(Expr.binop .add `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x - $y])   => `(Expr.binop .sub `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x * $y])   => `(Expr.binop .mul `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x / $y])   => `(Expr.binop .div `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x % $y])   => `(Expr.binop .mod `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x == $y])  => `(Expr.binop .eq `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x != $y])  => `(Expr.binop .ne `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x < $y])   => `(Expr.binop .lt `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x <= $y])  => `(Expr.binop .le `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x > $y])   => `(Expr.binop .gt `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x >= $y])  => `(Expr.binop .ge `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x && $y])  => `(Expr.binop .and `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x || $y])  => `(Expr.binop .or `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x ++ $y])  => `(Expr.binop .strAppend `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| !$x])       => `(Expr.unop .not `[RExpr| $x])
  | `(`[RExpr| $a[$i]])    => `(Expr.arrGet `[RExpr| $a] `[RExpr| $i])

/-! ## Helper macros for array/string expression forms -/

scoped syntax:max "arrLen(" term ")" : term
scoped syntax:max "strLen(" term ")" : term
scoped syntax:max "strGet(" term "," term ")" : term

scoped macro_rules
  | `(arrLen($a))      => `(Expr.arrLen `[RExpr| $a])
  | `(strLen($s))      => `(Expr.strLen `[RExpr| $s])
  | `(strGet($s, $i))  => `(Expr.strGet `[RExpr| $s] `[RExpr| $i])

/-! ## Radix type syntax -/

declare_syntax_cat rty
syntax "uint64" : rty
syntax "bool" : rty
syntax "string" : rty
syntax "unit" : rty
syntax rty "[]" : rty

syntax "`[RTy| " rty "]" : term

macro_rules
  | `(`[RTy| uint64]) => `(Ty.uint64)
  | `(`[RTy| bool])   => `(Ty.bool)
  | `(`[RTy| string]) => `(Ty.string)
  | `(`[RTy| unit])   => `(Ty.unit)
  | `(`[RTy| $t:rty[]]) => `(Ty.array `[RTy| $t])

/-! ## Statement syntax -/

declare_syntax_cat rstmt

-- Keyword-led forms
syntax "let " ident " : " rty " = " term ";" : rstmt
syntax "let " ident " := " "new " rty "[" term "]" ";" : rstmt
syntax "if " "(" term ")" " {" rstmt* "}" (" else " "{" rstmt* "}")? : rstmt
syntax "while " "(" term ")" " {" rstmt* "}" : rstmt
syntax "return " term ";" : rstmt

-- Identifier-led forms
syntax ident " := " term ";" : rstmt
syntax ident "(" term,* ")" ";" : rstmt
syntax ident "[" term "]" " := " term ";" : rstmt

syntax "`[RStmt|" rstmt* "]" : term

macro_rules
  | `(`[RStmt| ]) => `(Stmt.skip)
  | `(`[RStmt| $x:ident := $e:term;]) =>
    `(Stmt.assign $(Lean.quote x.getId.toString) `[RExpr| $e])
  | `(`[RStmt| let $x:ident : $t:rty = $e:term;]) =>
    `(Stmt.decl $(Lean.quote x.getId.toString) `[RTy| $t] `[RExpr| $e])
  | `(`[RStmt| let $x:ident := new $t:rty[$n:term];]) =>
    `(Stmt.alloc $(Lean.quote x.getId.toString) `[RTy| $t] `[RExpr| $n])
  | `(`[RStmt| if ($c) { $ts* } else { $es* }]) =>
    `(Stmt.ite `[RExpr| $c] `[RStmt| $ts*] `[RStmt| $es*])
  | `(`[RStmt| if ($c) { $ts* }]) =>
    `(Stmt.ite `[RExpr| $c] `[RStmt| $ts*] Stmt.skip)
  | `(`[RStmt| while ($c) { $bs* }]) =>
    `(Stmt.while `[RExpr| $c] `[RStmt| $bs*])
  | `(`[RStmt| $f:ident($args:term,*);]) => do
    let name := f.getId.toString
    let argExprs ← args.getElems.mapM fun a => `(`[RExpr| $a])
    if name == "free" then
      match argExprs with
      | #[e] => `(Stmt.free $e)
      | _ => Lean.Macro.throwError "free takes exactly one argument"
    else
      `(Stmt.callStmt $(Lean.quote name) [$[$argExprs],*])
  | `(`[RStmt| return $e:term;]) =>
    `(Stmt.ret `[RExpr| $e])
  | `(`[RStmt| $arr:ident[$idx:term] := $val:term;]) =>
    `(Stmt.arrSet (Expr.var $(Lean.quote arr.getId.toString)) `[RExpr| $idx] `[RExpr| $val])
  | `(`[RStmt| $s $ss*]) =>
    `(Stmt.seq `[RStmt| $s] `[RStmt| $ss*])

end Radix
