# cslib-v29-rc1

Lean 4 playground for algorithm verification using Lean v4.29.0-rc1, Mathlib, and [cslib](https://github.com/leanprover/cslib) (a library for reasoning about algorithm correctness and time complexity).

## Project structure

- `Playground/` — Lean source files with algorithm definitions and proofs
  - `MergeSort.lean` — merge sort with correctness and time complexity proofs
  - `PrefixSum.lean` — prefix sum / range sum with correctness proofs
- `lakefile.toml` — Lake build configuration (depends on cslib v4.29.0-rc1)

## Building

```
lake build
```

To build a single file:

```
lake build Playground.PrefixSum
```

## Iterating on proofs

When filling in a `sorry` or writing a new proof:

1. **Build frequently.** Run `lake build Playground.<Module>` after each change to get fast feedback. Don't try to write a long proof all at once.

2. **Search for existing lemmas.** Use leanexplore to find relevant theorems:
   ```
   https://www.leanexplore.com/api/search?q=<query>&pkg=Init&pkg=Batteries&pkg=Std&pkg=Mathlib
   ```
   For example, searching `List.foldl+length` or `List.take_take`. Include `&pkg=Mathlib` when searching for mathematical lemmas.

3. **Common proof strategies for list/array algorithms:**
   - For `foldl` properties, prove a generalized invariant (quantifying over `init`) by induction on the list, since the accumulator changes at each step.
   - For connecting custom definitions to standard ones (e.g. foldl-based prefix sum to `List.scanl`), prove an equivalence lemma first, then use existing library theorems (`getElem_scanl`, `sum_eq_foldl`, etc.).
   - Use `omega` for natural number arithmetic goals.
   - Use `simp` with targeted lemma arguments (e.g. `simp [List.length_append]`) rather than bare `simp` when possible.

4. **Working with `[i]!` (panicking access):** Convert to bounded `[i]` using `getElem!_pos` when you have an in-bounds proof, then apply library lemmas which are stated for bounded access.

5. **Typical proof iteration cycle:**
   - Write the proof term or tactic block
   - `lake build Playground.<Module>` to check
   - Read the error — "unsolved goals" shows the remaining goal state
   - Adjust tactics or search for the right lemma
   - Repeat
