/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

-- Core AST (types, values, operators, expressions, statements, programs)
import Radix.AST

-- Runtime infrastructure
import Radix.Heap
import Radix.Env
import Radix.State

-- Evaluation
import Radix.Eval.Expr
import Radix.Eval.Stmt
import Radix.Eval.Interp

-- Type checking
import Radix.TypeCheck

-- Concrete syntax
import Radix.Syntax

-- Optimizations
import Radix.Opt.ConstFold
import Radix.Opt.DeadCode
import Radix.Opt.CopyProp
import Radix.Opt.ConstProp
import Radix.Opt.Inline

-- Proofs
import Radix.Proofs.Determinism
import Radix.Proofs.TypeSafety
import Radix.Proofs.MemorySafety
import Radix.Proofs.InterpCorrectness

-- Linear ownership typing
import Radix.Linear

-- Examples
import Radix.Examples

-- Tests
import Radix.Tests.Basic
import Radix.Tests.Functions
import Radix.Tests.Arrays
import Radix.Tests.Strings
import Radix.Tests.Opt
import Radix.Tests.Linear

/-! # Radix: A Verified Embedded Imperative DSL

Radix is an imperative DSL embedded in Lean 4 with:
- **Types**: `uint64`, `bool`, `string`, `unit`, heap-allocated `array α`
- **Control flow**: `if/else`, `while`, `return`, function calls with frame isolation
- **Dynamic memory**: `alloc`, `free`, bounds-checked array access
- **Two semantics**: relational big-step (`BigStep`) and executable fuel-based (`Stmt.interp`)
- **Verified optimizations**: constant folding, dead code elimination, copy propagation,
  constant propagation, function inlining -- each with a mechanized proof that it
  preserves big-step semantics
- **Formal properties**: determinism, type preservation, memory safety (no use-after-free,
  no double-free), linear ownership typing with soundness proof
- **Concrete syntax**: `\`[RExpr| ...]` and `\`[RStmt| ...]` macros for natural notation

The architecture follows a classic compiler pipeline: AST -> type check -> optimize -> interpret.
Each optimization is a function `Stmt -> Stmt` paired with a theorem
`BigStep sigma s r -> BigStep sigma (s.opt) r`, ensuring semantic preservation.
-/
