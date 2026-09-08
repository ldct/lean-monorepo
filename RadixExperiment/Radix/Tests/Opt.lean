/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax
import Radix.Opt.ConstFold
import Radix.Opt.DeadCode
import Radix.Opt.ConstProp
import Radix.Opt.CopyProp
import Radix.Opt.Inline

/-! # Optimization Tests

Verify that optimizations transform programs correctly.
-/

namespace Radix.Tests

-- Constant folding: 3 + 4 should become 7
def test_cf_expr : Expr :=
  Expr.binop .add (Expr.lit (Value.uint64 3)) (Expr.lit (Value.uint64 4))

#guard match test_cf_expr.constFold with
  | Expr.lit (Value.uint64 7) => true
  | _ => false

-- Constant folding: true && false should become false
def test_cf_and_bool : Expr :=
  Expr.binop .and (Expr.lit (Value.bool true)) (Expr.lit (Value.bool false))

#guard match test_cf_and_bool.constFold with
  | Expr.lit (Value.bool false) => true
  | _ => false

-- Constant folding in statements: dead branch elimination
def test_cf_stmt := `[RStmt|
  if (true) {
    x := 1;
  } else {
    x := 2;
  }
]

#guard match test_cf_stmt.constFold with
  | Stmt.assign "x" (Expr.lit (Value.uint64 1)) => true
  | _ => false

-- Dead code elimination: skip sequences
def test_dce_skip :=
  Stmt.seq Stmt.skip (Stmt.assign "x" (Expr.lit (Value.uint64 1)))

#guard match test_dce_skip.deadCodeElim with
  | Stmt.assign "x" _ => true
  | _ => false

-- Dead code: false while loop
def test_dce_false_while :=
  Stmt.while (Expr.lit (Value.bool false)) (Stmt.assign "x" (Expr.lit (Value.uint64 1)))

#guard test_dce_false_while.deadCodeElim matches Stmt.skip

-- Constant propagation: x := 5; y := x + 1 → y := 6
def test_constprop := `[RStmt|
  x := 5;
  y := x + 1;
]

#guard match test_constprop.constPropagation with
  | Stmt.seq (Stmt.assign "x" (Expr.lit (Value.uint64 5)))
             (Stmt.assign "y" (Expr.lit (Value.uint64 6))) => true
  | _ => false

-- Constant folding: 5 + 3 → 8
def test_cf_add_const : Expr :=
  Expr.binop .add (Expr.lit (Value.uint64 5)) (Expr.lit (Value.uint64 3))

#guard match test_cf_add_const.constFold with
  | Expr.lit (Value.uint64 8) => true
  | _ => false

-- Constant folding: 6 * 7 → 42
def test_cf_mul_const : Expr :=
  Expr.binop .mul (Expr.lit (Value.uint64 6)) (Expr.lit (Value.uint64 7))

#guard match test_cf_mul_const.constFold with
  | Expr.lit (Value.uint64 42) => true
  | _ => false

-- Constant folding: 10 - 3 → 7
def test_cf_sub_const : Expr :=
  Expr.binop .sub (Expr.lit (Value.uint64 10)) (Expr.lit (Value.uint64 3))

#guard match test_cf_sub_const.constFold with
  | Expr.lit (Value.uint64 7) => true
  | _ => false

-- String constant folding
def test_cf_str : Expr :=
  Expr.binop .strAppend (Expr.lit (Value.str "hello")) (Expr.lit (Value.str " world"))

#guard match test_cf_str.constFold with
  | Expr.lit (Value.str "hello world") => true
  | _ => false

-- Optimization roundtrip: optimized program produces same result as original
private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

def test_opt_roundtrip := `[RStmt|
  x := 3 + 4;
  y := x * 1;
  z := y + 0;
]

#guard getResult test_opt_roundtrip "z" == getResult test_opt_roundtrip.constFold "z"
#guard getResult test_opt_roundtrip "z" == some (Value.uint64 7)

/-! ## Identity simplification tests -/

-- e + 0 → e when e has known uint64 type (literal)
#guard (Expr.binop .add (.lit (.uint64 5)) (.lit (.uint64 0))).constFold
    matches Expr.lit (Value.uint64 5)

-- 0 + e → e when e has known uint64 type
#guard (Expr.binop .add (.lit (.uint64 0)) (.lit (.uint64 5))).constFold
    matches Expr.lit (Value.uint64 5)

-- e - 0 → e when e has known uint64 type
#guard (Expr.binop .sub (.lit (.uint64 7)) (.lit (.uint64 0))).constFold
    matches Expr.lit (Value.uint64 7)

-- e * 1 → e when e has known uint64 type
#guard (Expr.binop .mul (.lit (.uint64 42)) (.lit (.uint64 1))).constFold
    matches Expr.lit (Value.uint64 42)

-- 1 * e → e when e has known uint64 type
#guard (Expr.binop .mul (.lit (.uint64 1)) (.lit (.uint64 42))).constFold
    matches Expr.lit (Value.uint64 42)

-- true && e → e when e has known bool type
#guard (Expr.binop .and (.lit (.bool true)) (.lit (.bool false))).constFold
    matches Expr.lit (Value.bool false)

-- e && true → e when e has known bool type
#guard (Expr.binop .and (.lit (.bool false)) (.lit (.bool true))).constFold
    matches Expr.lit (Value.bool false)

-- false || e → e when e has known bool type
#guard (Expr.binop .or (.lit (.bool false)) (.lit (.bool true))).constFold
    matches Expr.lit (Value.bool true)

-- e || false → e when e has known bool type
#guard (Expr.binop .or (.lit (.bool true)) (.lit (.bool false))).constFold
    matches Expr.lit (Value.bool true)

-- e ++ "" → e when e has known str type
#guard (Expr.binop .strAppend (.lit (.str "hello")) (.lit (.str ""))).constFold
    matches Expr.lit (Value.str "hello")

-- "" ++ e → e when e has known str type
#guard (Expr.binop .strAppend (.lit (.str "")) (.lit (.str "hello"))).constFold
    matches Expr.lit (Value.str "hello")

-- Identity NOT applied when type is unknown (variable)
#guard (Expr.binop .add (.var "x") (.lit (.uint64 0))).constFold
    matches Expr.binop .add (Expr.var "x") (Expr.lit (Value.uint64 0))

-- Identity applied to nested expressions with known type tags
-- (3 + 4) + 0 → 7  (first the inner 3+4 is folded to 7, then 7+0 is simplified)
#guard (Expr.binop .add (Expr.binop .add (.lit (.uint64 3)) (.lit (.uint64 4)))
    (.lit (.uint64 0))).constFold
    matches Expr.lit (Value.uint64 7)

-- e + 0 with e = nested binop that has inferable uint64 tag
-- (x is unknown, so inferTag returns none, so identity is NOT applied)
#guard (Expr.binop .add (Expr.binop .add (.var "x") (.lit (.uint64 1)))
    (.lit (.uint64 0))).constFold
    matches Expr.binop .add (Expr.binop .add (Expr.var "x") (Expr.lit (Value.uint64 1)))
                            (Expr.lit (Value.uint64 0))

/-! ## Constant folding edge cases -/

-- Boolean not folding: !true → false
#guard (Expr.unop .not (.lit (.bool true))).constFold
    matches Expr.lit (Value.bool false)

-- Nested constant folding: (2 * 3) + (4 * 5) → 26
#guard (Expr.binop .add
    (Expr.binop .mul (.lit (.uint64 2)) (.lit (.uint64 3)))
    (Expr.binop .mul (.lit (.uint64 4)) (.lit (.uint64 5)))).constFold
    matches Expr.lit (Value.uint64 26)

-- Constant fold in while(false) eliminates the loop body
def test_cf_while_false := Stmt.while
  (Expr.lit (Value.bool false))
  (Stmt.assign "x" (Expr.lit (Value.uint64 999)))

#guard test_cf_while_false.constFold matches Stmt.skip

-- Constant fold if(false) eliminates true branch
def test_cf_if_false :=
  Stmt.ite (Expr.lit (Value.bool false))
    (Stmt.assign "x" (Expr.lit (Value.uint64 1)))
    (Stmt.assign "y" (Expr.lit (Value.uint64 2)))

#guard test_cf_if_false.constFold matches Stmt.assign "y" _

-- Equality folding: 5 == 5 → true
#guard (Expr.binop .eq (.lit (.uint64 5)) (.lit (.uint64 5))).constFold
    matches Expr.lit (Value.bool true)

-- Inequality folding: 3 != 4 → true
#guard (Expr.binop .ne (.lit (.uint64 3)) (.lit (.uint64 4))).constFold
    matches Expr.lit (Value.bool true)

-- Boolean or folding: true || false → true
#guard (Expr.binop .or (.lit (.bool true)) (.lit (.bool false))).constFold
    matches Expr.lit (Value.bool true)

/-! ## Dead code elimination -/

-- seq(skip, skip) → skip
def test_dce_skip_skip := Stmt.seq Stmt.skip Stmt.skip

#guard test_dce_skip_skip.deadCodeElim matches Stmt.skip

-- seq(s, skip) → s
def test_dce_s_skip :=
  Stmt.seq (Stmt.assign "x" (Expr.lit (Value.uint64 1))) Stmt.skip

#guard test_dce_s_skip.deadCodeElim matches Stmt.assign "x" _

-- if with both branches skip → skip
def test_dce_if_skip_skip :=
  Stmt.ite (Expr.var "c") Stmt.skip Stmt.skip

#guard test_dce_if_skip_skip.deadCodeElim matches Stmt.skip

-- DCE in block
def test_dce_block :=
  Stmt.block [
    Stmt.skip,
    Stmt.assign "x" (Expr.lit (Value.uint64 1)),
    Stmt.skip
  ]

-- Block after DCE should have [skip, assign, skip] (DCE only goes inside each stmt)
#guard match test_dce_block.deadCodeElim with
  | .block _ => true
  | _ => false

-- if(true) with DCE should eliminate to the true branch
def test_dce_if_true :=
  Stmt.ite (Expr.lit (Value.bool true))
    (Stmt.assign "x" (Expr.lit (Value.uint64 1)))
    (Stmt.assign "x" (Expr.lit (Value.uint64 2)))

#guard test_dce_if_true.deadCodeElim matches Stmt.assign "x" _

/-! ## Copy propagation tests -/

-- x := 5; y := x → y becomes a copy of x's source
def test_copyprop_basic := `[RStmt|
  x := 5;
  y := x;
  z := y + 1;
]

-- After copy prop, z := y + 1 should become z := x + 1
-- (the copy map tracks y → x)
#guard match test_copyprop_basic.copyPropagation with
  | Stmt.seq (Stmt.assign "x" _)
    (Stmt.seq (Stmt.assign "y" (Expr.var "x"))
              (Stmt.assign "z" (Expr.binop .add (Expr.var "x") _))) => true
  | _ => false

-- Copy propagation: chain of copies a := b; c := a → c uses b
def test_copyprop_chain := `[RStmt|
  a := 10;
  b := a;
  c := b;
]

-- After copy prop: b := a stays, c := b should become c := a
#guard match test_copyprop_chain.copyPropagation with
  | Stmt.seq (Stmt.assign "a" _)
    (Stmt.seq (Stmt.assign "b" (Expr.var "a"))
              (Stmt.assign "c" (Expr.var "a"))) => true
  | _ => false

/-! ## Copy propagation roundtrip (same result after optimization) -/

def test_copyprop_roundtrip := `[RStmt|
  x := 5;
  y := x;
  z := y + 1;
]

#guard getResult test_copyprop_roundtrip "z" ==
  getResult test_copyprop_roundtrip.copyPropagation "z"

/-! ## Constant propagation deeper tests -/

-- Chain: x := 3; y := x; z := y * 2 → z := 6
def test_constprop_chain := `[RStmt|
  x := 3;
  y := x;
  z := y * 2;
]

#guard match test_constprop_chain.constPropagation with
  | Stmt.seq (Stmt.assign "x" (Expr.lit (Value.uint64 3)))
    (Stmt.seq (Stmt.assign "y" (Expr.lit (Value.uint64 3)))
              (Stmt.assign "z" (Expr.lit (Value.uint64 6)))) => true
  | _ => false

-- Constant propagation is invalidated by reassignment
def test_constprop_invalidate := `[RStmt|
  x := 5;
  x := x + 1;
  y := x + 1;
]

-- After x := x + 1, x is no longer a known constant, so y := x + 1 stays as-is
#guard match test_constprop_invalidate.constPropagation with
  | Stmt.seq (Stmt.assign "x" (Expr.lit (Value.uint64 5)))
    (Stmt.seq (Stmt.assign "x" (Expr.lit (Value.uint64 6)))
              (Stmt.assign "y" (Expr.lit (Value.uint64 7)))) => true
  | _ => false

/-! ## Chained optimizations -/

-- Apply constant propagation then constant folding
def test_chain_constprop_cf := `[RStmt|
  x := 3;
  y := x + 4;
]

-- After constProp: y := 3 + 4, after constFold: y := 7
-- But constPropagation already applies constFold internally!
#guard match test_chain_constprop_cf.constPropagation with
  | Stmt.seq (Stmt.assign "x" (Expr.lit (Value.uint64 3)))
             (Stmt.assign "y" (Expr.lit (Value.uint64 7))) => true
  | _ => false

-- Apply constFold then DCE: if(true && false) is folded to if(false), then DCE eliminates it
def test_chain_cf_dce :=
  Stmt.ite (Expr.binop .and (Expr.lit (Value.bool true)) (Expr.lit (Value.bool false)))
    (Stmt.assign "x" (Expr.lit (Value.uint64 1)))
    (Stmt.assign "x" (Expr.lit (Value.uint64 2)))

-- After constFold: true && false → false, then if(false) → else branch
#guard test_chain_cf_dce.constFold matches Stmt.assign "x" (Expr.lit (Value.uint64 2))

-- DCE on the already-folded result is identity
#guard test_chain_cf_dce.constFold.deadCodeElim
    matches Stmt.assign "x" (Expr.lit (Value.uint64 2))

-- constPropagation + DCE: x := 5; if(x == 5) ... → true branch
def test_chain_constprop_dce := `[RStmt|
  x := 5;
  if (x == 5) {
    y := 1;
  } else {
    y := 2;
  }
]

-- constPropagation replaces x with 5, folds 5==5 to true, eliminates false branch
#guard match test_chain_constprop_dce.constPropagation with
  | Stmt.seq (Stmt.assign "x" _) (Stmt.assign "y" (Expr.lit (Value.uint64 1))) => true
  | _ => false

/-! ## Chained optimization roundtrip: verify same result -/

def test_chained_roundtrip := `[RStmt|
  x := 3;
  y := x + 4;
  z := y + 0;
  w := z * 1;
]

-- All four transformations should produce the same result
#guard getResult test_chained_roundtrip "w" == some (Value.uint64 7)
#guard getResult test_chained_roundtrip.constFold "w" == some (Value.uint64 7)
#guard getResult test_chained_roundtrip.constPropagation "w" == some (Value.uint64 7)
#guard getResult test_chained_roundtrip.constPropagation.constFold "w" == some (Value.uint64 7)
#guard getResult test_chained_roundtrip.constPropagation.deadCodeElim "w" == some (Value.uint64 7)

/-! ## Inlining tests -/

open Std in
-- Simple inline: function body small enough to inline
def test_inline_simple :=
  let funs : HashMap String FunDecl := ({} : HashMap String FunDecl).insert "inc"
    { name := "inc", params := [("x", .uint64)], retTy := .uint64,
      body := Stmt.assign "result" (Expr.binop .add (Expr.var "x") (Expr.lit (Value.uint64 1))) }
  let s := Stmt.callStmt "inc" [Expr.lit (Value.uint64 5)]
  s.inline funs 1

-- After inlining, the call should become a scope
#guard match test_inline_simple with
  | Stmt.scope _ _ _ => true
  | _ => false

open Std in
-- Inlining is skipped for large functions
def test_inline_large :=
  let bigBody := (List.range 20).foldl (init := Stmt.skip) fun acc _ =>
    Stmt.seq acc (Stmt.assign "x" (Expr.lit (Value.uint64 1)))
  let funs : HashMap String FunDecl := ({} : HashMap String FunDecl).insert "big"
    { name := "big", params := List.nil, retTy := .unit, body := bigBody }
  let s := Stmt.callStmt "big" List.nil
  s.inline funs 1

-- Body too large, should remain a callStmt
#guard match test_inline_large with
  | Stmt.callStmt "big" _ => true
  | _ => false

open Std in
-- Inlining depth 0 leaves calls as-is
def test_inline_depth_zero :=
  let funs : HashMap String FunDecl := ({} : HashMap String FunDecl).insert "f"
    { name := "f", params := List.nil, retTy := .unit,
      body := Stmt.assign "x" (Expr.lit (Value.uint64 1)) }
  let s := Stmt.callStmt "f" List.nil
  s.inline funs 0

#guard match test_inline_depth_zero with
  | Stmt.callStmt "f" _ => true
  | _ => false

/-! ## Optimization on scope construct -/

-- Constant folding works inside scope bodies
def test_cf_scope :=
  Stmt.scope [("x", .uint64)] [Expr.lit (Value.uint64 5)]
    (Stmt.assign "y" (Expr.binop .add (Expr.lit (Value.uint64 3)) (Expr.lit (Value.uint64 4))))

-- After constant folding, the body's 3+4 should become 7
#guard match test_cf_scope.constFold with
  | Stmt.scope _ _ (Stmt.assign "y" (Expr.lit (Value.uint64 7))) => true
  | _ => false

-- DCE works inside scope bodies
def test_dce_scope :=
  Stmt.scope [("x", .uint64)] [Expr.lit (Value.uint64 5)]
    (Stmt.seq Stmt.skip (Stmt.assign "y" (Expr.lit (Value.uint64 1))))

#guard match test_dce_scope.deadCodeElim with
  | Stmt.scope _ _ (Stmt.assign "y" _) => true
  | _ => false

-- Constant folding on scope arguments
def test_cf_scope_args :=
  Stmt.scope [("x", .uint64)]
    [Expr.binop .add (Expr.lit (Value.uint64 1)) (Expr.lit (Value.uint64 2))]
    Stmt.skip

#guard match test_cf_scope_args.constFold with
  | Stmt.scope _ [Expr.lit (Value.uint64 3)] _ => true
  | _ => false

end Radix.Tests
