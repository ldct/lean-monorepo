import VersoSlides
import Verso.Doc.Concrete
import Radix

open VersoSlides

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

#doc (Slides) "Lean for AI, AI for Lean" =>

%%%
theme := "white"
slideNumber := true
transition := "slide"
%%%

# Lean for AI, AI for Lean

%%%
backgroundColor := "#312e81"
%%%

Leonardo de Moura

Lean FRO | March 2026

# The Result

10 AI agents built a *verified embedded DSL* with proved optimizations in *a single weekend*.

- Kernel-checked semantic and optimization proofs without `sorry`
- 5 verified compiler optimizations
- Determinism, type safety, memory safety — all proved
- Persistent allocations with ordinary array aliases
- Interpreter correctness — sound and complete
- Explicit rejection, byte I/O, and a checked C++ subset frontend

# Lessons Learned

- I did not touch the code. Zero lines. Full agent autonomy.
- Unlike most human users, Claude _reads the documentation_. One stuck agent? I said "Read the `grind` docs." It downloaded, understood, unblocked.
- Examples are powerful: agents found our DSL declaration examples and adopted the same pattern for Radix syntax.
- Claude struggled with _mutual induction_ — but found workarounds every time.
- Claude struggled with _monadic code_ and avoided it. We don't have enough examples for that.
- I created a GitHub token scoped to the Radix repo only. Good thing — Claude tried to push to `leanprover/lean4`.
- Toolchain version issues (v4.29.0) confused Claude when generating these slides.

# Radix — A Real Program

```lean -show
open Radix
```

Internal examples use Radix quotation macros. Verso elaborates every line. Benchmark proofs instead use the exact standalone C++ source files:

```lean
def slideBubbleSort := `[RStmt|
  let arr := new uint64[][10];
  arr[0] := 5; arr[1] := 3; arr[2] := 8;
  arr[3] := 1; arr[4] := 9; arr[5] := 2;
  arr[6] := 7; arr[7] := 4; arr[8] := 6;
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
]
```

# Big-Step Semantics — Explicit Outcomes

```lean
-- Big-step: ⟨σ, s⟩ ⇓ r
-- Normal completion, return, and rejection are distinct.
-- Sequences and loops propagate early return and rejection.
-- Calls share heap and streams.
-- Rejection crosses call boundaries.
example : BigStep σ .skip (.normal σ) :=
  BigStep.skip
example (he : e.eval σ = some v)
    (hs : σ.setVar x v = some σ') :
    BigStep σ (.assign x e) (.normal σ') :=
  BigStep.assign he hs
example (h₁ : BigStep σ₁ s₁ (.normal σ₂))
    (h₂ : BigStep σ₂ s₂ r) :
    BigStep σ₁ (s₁ ;; s₂) r :=
  BigStep.seqNormal h₁ h₂
example (hc : e.eval σ₁ = some (.bool true))
    (hb : BigStep σ₁ b (.normal σ₂))
    (hw : BigStep σ₂ (.while e b) r) :
    BigStep σ₁ (.while e b) r :=
  BigStep.whileTrue hc hb hw
```

# Determinism — `grind` Does The Work

```lean
-- Same state + same statement → same result
-- Proof by induction on h₁
-- grind closes equational contradictions
example (h₁ : BigStep σ s r₁)
    (h₂ : BigStep σ s r₂) : r₁ = r₂ :=
  BigStep.det h₁ h₂
```

In the real proof: `cases h₂ with | assign => grind` handles equational cases. `grind` decides contradictions like `some true = some false`. Explicit IH application for recursive cases (`seq`, `while`, `call`, `scope`).

# Interpreter Correctness — Sound and Complete

A fuel-based interpreter (`Stmt.interp`) proved equivalent to the relational semantics in both directions:

```lean
-- Completeness includes all three statement outcomes.
example (h : BigStep σ s r) :
    ∃ fuel, s.interp fuel σ =
      (r.outcome, r.state) :=
  Stmt.interp_complete h
-- Soundness: interp success implies BigStep
example (h : s.interp fuel σ = (.ok rv, σ')) :
    BigStep σ s (toStmtResult rv σ') :=
  Stmt.interp_sound h
```

The relational semantics has no fuel. The interpreter distinguishes successful completion, explicit rejection, runtime faults, and inconclusive fuel exhaustion. Soundness and completeness connect complete executions.

# Verified Optimizations — 5 Passes, 0 Sorry

```lean
-- Each pass: Stmt → Stmt with correctness theorem
-- "If the original runs, the optimized runs too"
example (h : BigStep σ s r) :
    BigStep σ s.constFold r :=
  Stmt.constFold_correct h
example (h : BigStep σ s r) :
    BigStep σ s.deadCodeElim r :=
  Stmt.deadCodeElim_correct h
example (h : BigStep σ s r) :
    BigStep σ s.copyPropagation r :=
  Stmt.copyProp_correct h
example (h : BigStep σ s r) :
    BigStep σ s.constPropagation r :=
  Stmt.constPropagation_correct h
example (h : BigStep σ s r) (hf : σ.funs = funs) :
    ∀ depth, BigStep σ (s.inline funs depth) r :=
  Stmt.inline_correct h hf
```

# Optimizations — What The Proofs Actually Look Like

*Constant folding:* `Expr.inferTag` conservatively infers output types to guard identity rules. `e + 0 → e` is sound when `e` produces `uint64`. `e * 0 → 0` is NOT sound — if `e` fails (e.g., out-of-bounds), the original returns `none` but the rewrite returns `some 0`.

*Copy propagation:* `CopyMap.agrees` invariant — every mapping `x → y` means `σ.getVar x = σ.getVar y`. Reset at control flow joins to stay sound.

*Inline:* rewrites `callStmt` into `scope` (frame-isolated body), bounded depth, non-recursive only. Proves function table invariant preserved through execution.

# Persistent Allocations

Arrays remain allocated until the execution ends. Copying an array reference preserves its identity, and aliases observe shared writes. Array access remains bounds checked.

There is no deallocation or ownership checker in the source language.

# The 10 Agents

%%%
transition := "fade"
%%%

Not 10 interchangeable "coding agents." 10 _domain experts_:

:::hstack

- _Chris Lattner_ — AST, IR, module structure
- _Simon Peyton Jones_ — types, syntax macros
- _Xavier Leroy_ — verification strategy
- _Adam Chlipala_ — proof engineering
- _Emina Torlak_ — type checking, tests

- _Derek Dreyer_ — semantics, memory model
- _John Regehr_ — edge cases, coverage
- _Dan Grossman_ — memory safety proofs
- _Nadia Polikarpova_ — formal specifications
- _Tiark Rompf_ — interpreter, optimizations

:::

All Claude. One weekend.

# The Surprise

%%%
transition := "fade"
%%%

The agents gave us _better feedback on Lean_ than our human users.

- More precise: structured error context, not "it doesn't work"
- More systematic: they hit every edge case, not just the one they needed
- More actionable: "tactic X fails on pattern Y because Z"

Adam's `grind` report was better than most human post-mortems.

# Optimize Lean for AI too, not just humans.

%%%
backgroundColor := "#312e81"
%%%

Nobody has built this yet.

# The Spec and The Feedback Loop

- _Better diagnostics:_ when a tactic fails, structured error metadata — not just prose. Claude happily processes them.
- _Links to documentation:_ tactic docstrings and error messages should contain links to the actual documentation. Claude reads them.
- _Faster startup:_ Claude can try different approaches more efficiently.
- _More examples:_ and instructions on how to find them. Claude started the Radix project by reading all our examples in the core repo.
- _Attribute guides:_ teach Claude how to use `@[simp]`, `@[grind]`, etc.
- _Implicit information:_ a pretty printer that shows implicit arguments and avoids exponential blowup. Claude claims it will help — confirming with Anthropic.

_Next experiment:_ Two agent teams in parallel. One builds a hard project and generates friction reports. The other patches Lean to eliminate the friction. We architect and steer.

# A Probable Future

%%%
backgroundColor := "#312e81"
%%%

- People will not write Lean. AI will write it. Humans read and audit.
- People will not write Verso. AI will produce lectures, papers, slides — with machine-checked math and code. Humans focus on the content.

Humans move up the stack. They become designers, architects, readers, auditors.
