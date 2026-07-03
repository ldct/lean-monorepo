# Plan: handle singular matrices in `intDetSimproc`

## Goal

After this work, `by simp only [intDetSimproc]` closes *every* determinant
goal for a concrete integer matrix up to 8×8 — both non-singular (current
behaviour) and singular (`det A = 0`). No extra `decide` needed at the
call site.

## Detection

With pivoting, `luDecompose` terminates whenever a non-zero pivot exists
in any row ≥ k; so `exactMinScaling` returning `none` is equivalent to
`A` being rationally singular, i.e. `det A = 0`. The trigger is the
existing meta-side check `LUMinScaling.det qmat == 0`.

Top-level simproc flow:

```
case exactMinScaling qmat of
| some data → existing pivoted-LU witness  (det A = d)
| none      → singular path                (det A = 0)
```

## Strategy: kernel-vector witness

Over an integral domain, if `A.mulVec v = 0` for some `v ≠ 0` then
`det A = 0` (standard adjugate argument). We use this:

```
lemma det_eq_zero_of_mulVec_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (v : Fin n → ℤ) (hv : v ≠ 0) (h : A.mulVec v = 0) : A.det = 0
```

The simproc produces a concrete integer kernel vector `v`, and
discharges `v ≠ 0` and `A.mulVec v = 0` via `mkDecideProof`. Both
propositions are cheap under kernel reduction:

- `v ≠ 0` reduces to a finite disjunction `v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ …`,
  i.e. checking n integers against zero.
- `A.mulVec v = 0` reduces to n component equalities, each an n-term
  sum of integers.

Total kernel work: O(n²). Negligible at n=8.

## Mathlib scout (milestone 0)

Need `det_eq_zero_of_mulVec_eq_zero` (name TBD). Candidate searches:

- `Matrix.eq_zero_of_mulVec_eq_zero`
- `Matrix.isUnit_iff_exists_mulVec_ne_zero`
- `Matrix.mulVec_injective_iff_isUnit`

If no direct lemma exists, the hand proof is ~10 lines via
`Matrix.mul_adjugate`:
```
A * adjugate A = det A • 1
A.mulVec (adjugate A * v) = det A • v
v ≠ 0 ∧ integral domain ⇒ det A • v = 0 ⇒ det A = 0
```

## Finding `v` in meta

Gaussian elimination over ℚ to row-echelon form; locate the first zero
row (guaranteed to exist since the matrix is singular); back-substitute
to produce a ℚ-kernel vector; clear denominators by multiplying by the
LCM.

Implementation option: **reuse the partial LU state**. When
`luDecompose` gives up at column `k`, it's already computed L[0..k-1],
U[0..k-1], and the pivoted A. The dependence that blocked it tells us
a rational linear combination of rows `0..k` vanishes in the first `k+1`
columns. Working out the exact combination from L and the elimination
history gives `v`.

Alternatively (simpler to code): **ignore the partial LU and do a
fresh REF computation**. At n ≤ 8 the cost is trivial and the code is
cleaner.

Recommend starting with the fresh-REF version; switch to partial-LU
reuse only if there's a reason.

## Milestones

### Milestone 0 — Mathlib scout + bridge lemma

* Locate (or write) `det_eq_zero_of_mulVec_eq_zero`.
* Add it to `IntDetSimproc.lean` alongside `det_of_smul_det`.
* Verify a hand-written usage closes with only standard axioms:
  ```
  example : (!![1,2;2,4] : Matrix _ _ ℤ).det = 0 :=
    det_eq_zero_of_mulVec_eq_zero ![2, -1] (by decide) (by decide)
  ```

**Demonstration:** the hand example closes cleanly; `#print axioms`
shows only `propext, Classical.choice, Quot.sound`.

### Milestone 1 — kernel-vector finder

* Add `findKernelVector : QMat → Option (List Int)`:
  1. Gaussian-eliminate over ℚ (full pivoting, tracking row/col ops)
     until a zero row appears.
  2. Read off the free variable from the zero row's position.
  3. Back-substitute to get a rational kernel vector.
  4. Multiply by `lcmList` of denominators → integer `v`.
  5. Return `none` if anything unexpected happens (defensive;
     shouldn't trigger for truly singular matrices).
* Standalone `#eval` tests on:
  * `[[1, 2], [2, 4]]` → expect `v` proportional to `[2, -1]`.
  * `[[1, 2, 3], [4, 5, 6], [7, 8, 9]]` → rank 2, `v` in kernel.
  * An 8×8 rank-7 matrix.

**Demonstration:** `#eval` outputs pass the condition `Av = 0 ∧ v ≠ 0`
(also verify inside the helper).

### Milestone 2 — wire into the simproc

* New branch triggered when `exactMinScaling qmat = none ∧
  LUMinScaling.det qmat == 0`:
  1. Call `findKernelVector qmat` (return `.continue` on unexpected
     `none`).
  2. Build `vExpr : Fin n → ℤ` as a concrete literal (use the same
     `matOfList`-style trick — either `fun i => (vList.getD i.val 0)`
     wrapped in `Function.of`, or directly as a vector literal).
  3. `mkDecideProof` of `vExpr ≠ 0` and `A.mulVec vExpr = 0`.
  4. Apply `det_eq_zero_of_mulVec_eq_zero` to combine; emit the `det A
     = 0` rewrite.

**Demonstration:** `simp only [intDetSimproc]` closes
`Sing.det = 0` (existing 2×2 test) with no trailing `decide`. Drop the
`decide` from the test file.

### Milestone 3 — tests & axiom check

Singular cases at n ∈ {2, 3, 4, 6, 8}:

* Row or column of zeros.
* Two equal rows.
* Rank-deficient: a row equals a linear combo of the others.
* 8×8 rank-7 from zeroing a row of `E₈`.

Each closes with `simp only [intDetSimproc]` alone; `#print axioms`
reports only the standard three.

## Open questions

1. **Does a ready-made Mathlib lemma exist?** If yes, milestone 0 is
   a five-minute search; if not, ~10 lines of hand-proving.

2. **Can `exactMinScaling` ever return `none` for a non-singular
   matrix?** With pivoting, no — but keep a defensive sanity check
   (`LUMinScaling.det qmat == 0`) so we never silently emit a wrong
   `det = 0` proof.

## Out of scope

* Proving `det ≠ 0` without computing the value (not useful here).
* Reporting the rank of singular matrices.
* Handling rings other than ℤ — covered separately in
  `IntDetSimprocPID_PLAN.md`.
