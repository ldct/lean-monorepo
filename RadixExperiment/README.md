# RadixExperiment

Radix is a verified embedded DSL built entirely by 10 AI agents (all Claude) in a single weekend.
This repository contains the Radix source code and a [Verso](https://github.com/leanprover/verso)-based slide deck
presenting the results: **"Lean for AI, AI for Lean"**.

## What Radix demonstrates

- **Zero `sorry`** — 52 theorems, all complete
- 5 verified compiler optimizations (constant folding, dead code elimination, copy propagation, constant propagation, inlining)
- Big-step semantics (16 rules) with determinism proof
- Interpreter correctness — sound and complete w.r.t. relational semantics
- Linear ownership typing with soundness proof (644-line invariant preservation)
- 27 modules, ~7,400 lines of Lean

Zero lines were written by a human. The agents had full autonomy.

## Examples

Radix programs are written using concrete syntax macros (`[RStmt|...]`) that Lean elaborates and type-checks:

```lean
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
```

Heap-allocated arrays with manual memory management:

```lean
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
```

Function definitions with heap communication between caller and callee:

```lean
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
    arr[0] := 10; arr[1] := 20; arr[2] := 30;
    zeroOut(arr, 3);
    val := arr[0];
  ]
}

#eval! runProg zeroArray "val"
-- 0 (was 10 before the function call)
```

## Key theorems

**Determinism** — same state + same statement implies identical result:

```lean
theorem BigStep.det (h₁ : BigStep σ s r₁) (h₂ : BigStep σ s r₂) : r₁ = r₂
```

**Interpreter correctness** — a fuel-based interpreter proved equivalent to the relational semantics in both directions:

```lean
-- Completeness: BigStep implies interp succeeds
theorem Stmt.interp_complete (h : BigStep σ s r) :
    ∃ fuel, s.interp fuel σ = (.ok r.retVal, r.state)

-- Soundness: interp success implies BigStep
theorem Stmt.interp_sound (h : s.interp fuel σ = (.ok rv, σ')) :
    BigStep σ s (toStmtResult rv σ')
```

**Verified optimizations** — each compiler pass preserves semantics:

```lean
theorem Stmt.constFold_correct (h : BigStep σ s r) : BigStep σ s.constFold r
theorem Stmt.deadCodeElim_correct (h : BigStep σ s r) : BigStep σ s.deadCodeElim r
theorem Stmt.copyProp_correct (h : BigStep σ s r) : BigStep σ s.copyPropagation r
theorem Stmt.constPropagation_correct (h : BigStep σ s r) : BigStep σ s.constPropagation r
theorem Stmt.inline_correct (h : BigStep σ s r) (hfuns : σ.funs = funs) :
    ∀ depth, BigStep σ (s.inline funs depth) r
```

**Linear ownership soundness** — the three-part invariant (heap well-formedness, liveness, distinctness) is preserved through execution:

```lean
theorem LinearOk.soundness
    (hlin : LinearOk O s O')
    (hstep : BigStep σ s (.normal σ'))
    (hinv : OwnershipInv σ O)
    (hwt : WellTypedFuns σ.funs) :
    OwnershipInv σ' O'
```

Every owned variable holds a live, distinct heap address:

```lean
theorem LinearOk.live_access
    (hlin : LinearOk O s O')
    (hstep : BigStep σ s (.normal σ'))
    (hinv : OwnershipInv σ O)
    (hwt : WellTypedFuns σ.funs)
    (hx : x ∈ O') :
    ∃ a, σ'.getVar x = some (.addr a) ∧ σ'.heap.lookup a ≠ none
```

## Repository structure

- `Radix/` — the DSL: AST, semantics, type checker, interpreter, optimizations, proofs, syntax macros
- `Slides.lean` — slide content (Verso markup with embedded Lean)
- `Main.lean` — build entry point and HTML post-processing
- `static/` — custom CSS and assets for the slide deck

## Building

Requires [Lean 4](https://lean-lang.org) and [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```bash
lake build
.lake/build/bin/radix-slides
# Output goes to _out/
```

## License

Apache-2.0