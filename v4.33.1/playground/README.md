# Lean 4.33.1 stock playground

This is a stock `leanprover/lean4:v4.33.1` playground. It matches the layout,
Lake options, and Mathlib v4.33.1 pin of `v4.33.1-optimized/playground`, while
using the prebuilt standard Mathlib cache independently.

```sh
cd v4.33.1/playground
lake build
lake env lean Playground/Scratch.lean
```

The cached packages under `.lake/packages` are an APFS clone of the optimized
project's downloaded standard cache. They are not built from source here,
including native tactic artifacts.
