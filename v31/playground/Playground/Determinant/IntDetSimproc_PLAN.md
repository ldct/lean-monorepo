# Plan: `intDetSimproc` — integer-matrix determinants via scaled LU

## Goal

A simproc that rewrites `Matrix.det A` to an integer literal, where
`A : Matrix (Fin n) (Fin n) ℤ` is a concrete literal (`!![ … ]`) of size
up to 8×8. Larger sizes are out of scope for this plan — we'll revisit
performance and `decide +kernel` blowup once the 8×8 case works end-to-end.

Strategy mirrors `Determinant5.lean` (`E₈_det'`): scale `A` by the smallest
positive integer `k` such that `k • A` admits an integer LU factorisation,
then recover `det A` from `det L * det U = k^n * det A`.

## Mathematical kernel

Given integer `A : Matrix (Fin n) (Fin n) ℤ` with `det A ≠ 0` and
pivotless LU over ℚ, `LUMinScaling.exactMinScaling` returns:

- `n_min : ℕ` — the minimal positive scalar
- `L_int, U_int : QMat` with **integer entries**
- satisfying `L_int * U_int = n_min • A` (as rational matrices), with
  `L_int` lower triangular and `U_int` upper triangular.

Then
```
det(n_min • A) = (n_min)^n * det A      -- Matrix.det_smul
det L_int * det U_int = det(n_min • A)  -- det_mul + the factorisation
det L_int, det U_int = ∏ diag           -- triangularity
⇒ det A = (∏diag L_int) * (∏diag U_int) / n_min^n
```
Division is exact; we prove the multiplicative form and cancel `n_min^n`
via `det_of_smul_det` (already present in `Determinant5.lean`).

## File layout

Final state:

- `Playground/Determinant/IntDetSimproc.lean` — simproc + helpers.
- `Playground/Determinant/IntDetSimprocTest.lean` — golden tests.
- `Playground/LUMinScaling.lean` — gains `det_of_smul_det` (moved from
  `Determinant5`) so it's colocated with `exactMinScaling`.

## Milestones

Each milestone is a working, committable state: the file compiles, an
example reduces as far as the milestone promises, and the remaining work
is clearly scoped. Each milestone can be inspected by the user.

### Milestone 0 — scaffolding

- Create `IntDetSimproc.lean` with imports (`Mathlib`,
  `Playground.LUMinScaling`) and an empty namespace `IntDetSimproc`.
- Move `det_of_smul_det` from `Determinant5` into `LUMinScaling`; update
  `Determinant5` to `open`/reuse. Confirm `Determinant5` still builds.
- Add a stub `simproc_decl intDetSimproc (Matrix.det _) := fun _ =>
  return .continue` so downstream files can already reference the name.

**Demonstration:** `example : True := by simp only [intDetSimproc]; trivial`
compiles.

### Milestone 1 — rewrite `det A` to `det (n_min • A)` form

Scope: extract `A` from the expression, call `exactMinScaling`, and emit
the rewrite

```
det A  ⟿  (det ((n_min : ℤ) • A)) / n_min ^ n        -- n_min, n literals
```

More precisely, we do **not** emit division; we rewrite to
`det A = d` where `d` is the integer literal we plan to return, but we
keep everything else opaque for now: we discharge the proof obligation
with `sorry`. This lets us exercise all the meta-level plumbing
(expression walking, `evalExpr`, `exactMinScaling`, literal
construction) with the proof wiring stubbed out.

Also in this milestone:

- `evalIntMatrixExpr : Expr → MetaM (Option (Nat × List (List Int)))`
  using `Lean.Meta.evalExpr` (pattern from `Determinant1.evalIntExpr`).
- Handle `n = 0` (return `1`) and `n = 1` (return `A 0 0`) specially —
  skip LU.

**Demonstration:** `example : E₈.det = 1 := by simp only [intDetSimproc]`
closes the goal modulo one `sorry` in the simproc-generated proof. The
`#check` of the generated term shows the right literal. Add a
`set_option linter.unusedTactic false` or similar so the `sorry` is loud
but expected.

### Milestone 2 — prove the scaling step

Replace the first `sorry` with a real proof that
`(n_min : ℤ) • A = L_int * U_int`, where `L_int` and `U_int` are the
integer matrices produced by `exactMinScaling`, materialised as `!![ … ]`
literals in the proof term.

Concretely the simproc now emits:

```
det_of_smul_det (k := n_min) (by decide)
  (show ((n_min : ℤ) • A).det = (n_min : ℤ) ^ n * d from by
     rw [show (n_min : ℤ) • A = L_int * U_int from by decide +kernel]
     sorry)   -- det (L_int * U_int) = n_min ^ n * d remains
```

Key subtask: construct `L_int` and `U_int` as `Expr`s in the
`Matrix (Fin n) (Fin n) ℤ` shape (`Matrix.of ![![…]]`). Likely easiest
to build them as `Syntax` via `` `(!![ $rows,* ]) `` and elaborate.

**Demonstration:** `E₈.det = 1` reduces, with one `sorry` left (the
`det L * det U` computation). Use `#print axioms` on the test to see
only `sorryAx` remaining.

### Milestone 3 — prove the triangular determinant step

Close the remaining `sorry` by emitting:

```
rw [Matrix.det_mul,
    show L_int.det = detL from by
      rw [Matrix.det_of_lowerTriangular]
      · decide +kernel
      · unfold Matrix.BlockTriangular; decide +kernel,
    show U_int.det = detU from by ...symmetric...]
decide +kernel   -- closes n_min ^ n * d = detL * detU as an integer equality
```

where `detL = ∏ diag L_int`, `detU = ∏ diag U_int`, and
`detL * detU = n_min ^ n * d` is verified at meta time.

**Demonstration:** `#print axioms E₈_det_via_simproc` shows **no**
`sorryAx`. `example : E₈.det = 1 := by simp only [intDetSimproc]`
closes on its own.

### Milestone 4 — tests and edge cases

Add `IntDetSimprocTest.lean`:

- 2×2 with `det = 1` (smallest non-trivial).
- 3×3 with `det ≠ ±1` (catches cancellation off-by-one).
- 4×4 with fractions in the ℚ-LU (exercises `n_min > 1`).
- `E₈` from `Determinant1` (8×8, `det = 1`).
- A random 8×8 integer matrix with `det ≠ 1`, verified against a
  hand-computed value.
- Singular matrix — simproc no-ops (doesn't loop or fail).
- Matrix whose ℚ-LU needs a permutation — simproc no-ops.

Also: add a `set_option maxHeartbeats` check on the 8×8 test so we
notice if `decide +kernel` regresses.

**Demonstration:** whole test file builds under default heartbeats.

## Proof construction details

Build proof terms via `` `(…) `` quotations elaborated in `MetaM`, not
hand-rolled `Expr`s — `L_int` and `U_int` literals are far easier to
write as `!![ … ]` syntax. The pattern is roughly:

```
let lSyn ← mkMatrixLitSyntax lInt   -- `!![ … ]`
let uSyn ← mkMatrixLitSyntax uInt
let proofSyn ← `(det_of_smul_det (k := $(mkNatLit n_min)) (by decide) …)
let proof ← elabTermEnsuringType proofSyn (← mkEq origDet dLit)
```

All `decide +kernel` goals are closed because `L_int`, `U_int`, `n_min`,
`d` are ground integer literals.

## Edge cases

- **`n = 0`**: `det A = 1`, short-circuit.
- **`n = 1`**: `det A = A 0 0`, short-circuit; no LU needed.
- **Singular `A`**: `exactMinScaling` returns `none` ⇒ `.continue`.
  (Don't claim `det A = 0` — `luDecompose` failure ≠ singular.)
- **Needs permutation**: `.continue`. Out of scope for this plan.
- **Non-concrete `n` or non-`ℤ` entries**: `.continue`.

## Open questions

1. **Does `decide +kernel` scale to 8×8 entrywise matrix equality?**
   64 integer comparisons — should be fine, verify in milestone 3.
2. **Keep `det_of_smul_det` generic over the base ring?** `Determinant5`
   has it at ℤ. For this simproc ℤ is enough; leave as-is for v1.
3. **Tactic wrapper (`int_det`)?** Deferred until after milestone 4.
