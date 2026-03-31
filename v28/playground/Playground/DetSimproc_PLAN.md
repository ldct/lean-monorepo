# Plan: `detSimproc` — a simproc for integer matrix determinants

## Goal

Write a `simproc` that rewrites `M.det` (for a concrete `Matrix (Fin n) (Fin n) ℤ`) to a
numeral, producing a proof via row reduction — the same strategy used manually in
`Determinant1.lean`.

Desired usage:
```lean
example : E₈.det = 1 := by simp only [detSimproc]
```

## Architecture

The simproc has two halves:
1. **Meta-level computation** (in `MetaM`): extract the matrix, run Gaussian elimination,
   choose the row operations.
2. **Proof construction**: chain together lemma applications that justify each row operation,
   ending with an upper-triangular determinant calculation.

## Detailed steps

### Step 0: Foundation lemmas (pure Lean)

We already have `my_helper`. Generalize it slightly and add a companion for row swaps:

```lean
-- Row combination: row[i] ← a·row[i] + b·row[j], det scales by a
lemma det_rowCombine {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ} (i j : Fin n) (a b : ℤ)
    (h : (M.updateRow i (a • M i + b • M j)).det = a * k)
    (hij : i ≠ j) (ha : a ≠ 0) :
    M.det = k

-- Row swap: swapping rows i and j negates the determinant
lemma det_rowSwap {M : Matrix (Fin n) (Fin n) ℤ} {k : ℤ} (i j : Fin n)
    (h : (M.submatrix (Equiv.swap i j) id).det = -k)
    (hij : i ≠ j) :
    M.det = k
```

The row-swap lemma is needed when the natural pivot is zero and we must permute rows.
(For many matrices including E₈ no swaps are needed, but we should handle the general case.)

We also need:
```lean
-- Upper-triangular finish: for the base case after elimination
lemma det_upper_triangular_eq {M : Matrix (Fin n) (Fin n) ℤ}
    (h_tri : M.BlockTriangular id) (h_prod : ∏ i, M i i = k) :
    M.det = k
```

### Step 1: Extract the matrix (MetaM)

Pattern-match on `Matrix.det M` where `M : Matrix (Fin n) (Fin n) ℤ`.

Extract entries by reducing `M i j` for each `i j : Fin n`:
- Build `Fin n` literals using `mkApp2 (.const ``Fin.mk) nExpr iExpr` (with proof of `i < n`).
- Use `whnf` to reduce `M (Fin.mk i _) (Fin.mk j _)` to an integer literal.
- Collect into a `n × n` array of `Int` values.

This is the trickiest part — matrices may be defined via `!![ ... ]`, `Matrix.of`,
`fun i j => ...`, etc.  Using `whnf` on `M i j` handles all representations uniformly.

### Step 2: Gaussian elimination (pure computation)

Run standard column-pivoted Gaussian elimination over `ℤ` on the extracted array.
At each column `c`:

1. **Find pivot**: scan rows `c..n-1` for a nonzero entry in column `c`.
   Prefer the entry that minimizes the resulting coefficients (smallest absolute value).
2. **Swap** (if pivot ≠ diagonal): record a row swap `(i, c)` and negate sign tracker.
3. **Eliminate** below: for each row `r > c` with nonzero `M[r][c]`:
   - Compute `a = M[c][c]`, `b = -M[r][c]` (so `a·row[r] + b·row[c]` zeros column `c`).
   - Actually: use `a = pivot / g`, `b = -entry / g` where `g = gcd(pivot, entry)` to
     keep entries from exploding. The scale factor is `a`.
   - Record the operation `(r, c, a, b)` and update the working matrix.

Output: a list of operations `(swap | combine)` and the final upper-triangular matrix.

Compute the expected determinant:
```
det = (∏ diagonal of final matrix) / (∏ scale factors) * sign
```
Verify this is an exact integer division (it always will be if the algorithm is correct).

### Step 3: Build the proof term (MetaM)

Walk the operation list **backwards** (innermost operation first), building the proof
term from the inside out:

1. **Base case**: The innermost goal is `finalMatrix.det = diag_product`.
   Prove via `det_of_upperTriangular` + `decide +kernel` (or `native_decide`).
   
   Actually, for the simproc we need to build this as an `Expr`. Options:
   - Use `mkDecideProof` for the `BlockTriangular` condition and the product equality.
   - Or use `native_decide` — but that's not available in simprocs.
   - Best approach: prove `BlockTriangular id` and `∏ i, M i i = k` each by `decide`.

2. **Inductive case**: For each row operation (working outward):
   - For a **combine** `(r, c, a, b)`: apply `det_rowCombine` with the appropriate
     `Fin n` indices, integer literals, and `decide` proofs for `i ≠ j` and `a ≠ 0`.
   - For a **swap** `(i, j)`: apply `det_rowSwap` with `decide` proof of `i ≠ j`.
   - The hypothesis `h` is the proof from the previous (inner) step.

   The key subtlety: each application of `det_rowCombine` changes the goal's matrix.
   We don't explicitly build the intermediate matrix expressions — Lean's unifier does
   that. We just need the proof to typecheck. Specifically:
   - `det_rowCombine i j a b h ...` has type `M.det = k`
   - where `h : (M.updateRow i (a • M i + b • M j)).det = a * k`
   - Lean must verify that the `M.updateRow ...` expression matches the matrix from
     the inner proof. This should work because everything is definitionally equal.

3. **Performance concern**: The `decide` proofs inside the chain (for `i ≠ j`, `a ≠ 0`)
   are trivial — just `Fin` and `Int` inequality. The expensive `decide` is only at
   the base case (upper-triangular check + product).

### Step 4: Assemble the simproc

```lean
simproc_decl detSimproc (Matrix.det _) := fun e => do
  -- 1. Match Matrix.det M, extract n, verify type is ℤ
  -- 2. Extract n×n integer entries via whnf
  -- 3. Run Gaussian elimination → operations list + determinant value
  -- 4. Build chained proof term
  -- 5. Return .done { expr := intLit det, proof? := proof }
```

The simproc returns `.done` with:
- `expr`: the determinant as an integer literal expression
- `proof?`: the proof that `M.det = <literal>`

### Step 5: Handle `M.det = k` goals

The simproc above rewrites `M.det` to a numeral. If the user writes:
```lean
example : E₈.det = 1 := by simp only [detSimproc]
```
`simp` will rewrite the LHS to `1`, producing `1 = 1`, which closes by `rfl`.

## Alternative: tactic instead of simproc

A simproc is cleaner (works in `simp` pipelines, in hypotheses, etc.), but an
alternative is a standalone `det_decide` tactic that:
1. Matches the goal `M.det = ?k` or `M.det = k`
2. Runs the same extraction + elimination
3. Closes the goal directly via `exact proof`

This is simpler to implement (no need to return an `Expr` for the result, just close
the goal). Could be a good first milestone.

## Implementation plan / milestones

### Milestone 1: Tactic for concrete `Fin n` matrices
- [ ] Write `det_rowCombine` and `det_upper_triangular_eq` lemmas
- [ ] Write a `MetaM` function to extract entries from a `Matrix (Fin n) (Fin n) ℤ`
- [ ] Write the Gaussian elimination algorithm (pure Lean, `Array (Array Int)`)
- [ ] Write proof-term builder that chains `det_rowCombine` applications
- [ ] Package as a tactic `det_compute` that closes `M.det = k`
- [ ] Test on E₈ and a few other matrices

### Milestone 2: Simproc wrapper
- [ ] Wrap the tactic core as `simproc_decl detSimproc (Matrix.det _)`
- [ ] Test with `simp only [detSimproc]`
- [ ] Test in hypothesis position

### Milestone 3: Robustness
- [ ] Handle row swaps (zero pivots)
- [ ] Handle 0×0 and 1×1 matrices as special cases
- [ ] Handle `ℚ`, `ℝ` matrices (extract integer matrix if entries happen to be integers)
- [ ] Performance: test on 16×16, 20×20 matrices
- [ ] Better pivot selection to keep intermediate entries small

### Milestone 4: Polish
- [ ] Good error messages when extraction fails
- [ ] Support `Matrix (Fin n) (Fin n) ℕ` (via cast to ℤ?)
- [ ] Documentation and examples

## Key risks / open questions

1. **Entry extraction**: Can `whnf` reliably reduce `M i j` to a numeral for matrices
   defined via `!![ ]`? Need to test. May need to unfold specific definitions first.

2. **Proof term size**: For an `n×n` matrix, we produce `O(n²)` row operations.
   Each produces a proof term. For n=8 this is ~28 operations — fine. For n=20
   this is ~190 — probably still fine but worth benchmarking.

3. **Base case cost**: The `decide` proof for `BlockTriangular` + diagonal product
   on the final matrix. For `Fin n` with small `n`, `decide` should handle this.
   If it's slow, we can break it into per-entry proofs.

4. **`updateRow` reduction**: When Lean unfolds `M.updateRow i (a • M i + b • M j)`,
   does it produce something that `decide` can handle efficiently? Or do we need
   to prove the intermediate matrix equals a concrete literal? If so, we'd need
   an additional `show M.updateRow ... = !![ ... ]` step (provable by `decide`/`ext`).

5. **Coefficient growth**: Fraction-free elimination over ℤ can produce large
   intermediate entries. Using GCD-reduced coefficients (Bareiss-like) helps.
   For the proof, we only need the `a` and `b` values to be correct — the actual
   intermediate matrix entries are computed by Lean's kernel.

## File layout

```
Playground/
  DetSimproc.lean          -- the simproc + tactic
  DetSimproc/
    Lemmas.lean            -- foundation lemmas (det_rowCombine, etc.)
    GaussElim.lean         -- pure-Lean Gaussian elimination algorithm
    Extract.lean           -- MetaM code to extract matrix entries
    ProofBuilder.lean      -- MetaM code to build proof terms
  Determinant1.lean        -- existing test case (E₈)
  DetSimproc_PLAN.md       -- this file
```
