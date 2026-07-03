# Plan: extend `intDetSimproc` to PIDs (focus: ℤ[X], char poly)

## Goal

Generalise the simproc so it computes determinants of square matrices
over any PID `R` whose field of fractions `F = Frac R` admits exact
arithmetic in meta. The motivating instance is `R = ℤ[X]`,
`F = ℚ(X)`, which gives us **characteristic polynomials** of integer
matrices essentially for free: `charpoly A = det(X • 1 - A)`.

We aim for matrix sizes up to 8×8, same as the current ℤ simproc.

## What stays the same

The math skeleton is unchanged:

```
LU  in F:    L_F * U_F = perm(A)            -- exact in F
scaling:     L_F * U_F * d = perm(A) * d    -- d ∈ R chosen so L*U has R-entries
det:         det(L) * det(U) = d^n * sign(σ) * det(A)
```

So `det A = sign(σ) * (∏ diag L) * (∏ diag U) / d^n`, with the division
exact in `R`. The witness predicate `intDetWitnessPerm` already
generalises over any `CommRing` — only the meta-side computation is
ring-specific.

What's ring-specific:

- The **meta arithmetic** for LU over `F`: how to add/mul/div elements,
  how to compute the scaling factor `d`.
- The **`Decidable` cost** of `k ≠ 0`, matrix equality, triangularity,
  diagonal product equalities, and `Equiv.Perm.sign σ * k^n * d = …`.
  All exist for `R = ℤ[X]` via `DecidableEq (Polynomial ℤ)`, but kernel
  reduction may be slow.

## Approach options

Two reasonable architectures:

**A. Generic over `R`, with a meta-side typeclass.** Keep the Lean
   lemma `det_eq_of_witnessPerm` polymorphic. Drive the simproc by an
   abstract "MetaRing" interface that tells it how to do the LU and
   build the witness for a particular `R`. Clean, but more upfront
   plumbing.

**B. One ring at a time.** Duplicate the simproc for each `R` we care
   about (ℤ, ℤ[X], ℚ). Each instance has its own meta arithmetic and
   witness type, but they all call the same generic Lean lemma. Less
   abstraction, faster to ship the first instance.

Recommend **B for the first version** (ℤ[X]) and refactor to A only if
we add a third ring.

## Why ℤ[X] is the right next target

- `Frac ℤ[X] = ℚ(X)`, exact arithmetic possible (rational functions).
- Application: char poly of an integer matrix is `det(X • 1 - A)`,
  which is a determinant of an `(ℤ[X])`-valued matrix. **No new
  Lean theory needed** beyond what the simproc itself provides.
- Same algorithm (LU + minimal scaling) works because ℤ[X] is a UFD.
- The "minimal scaling" `d` becomes a polynomial; the integer case is
  just the degree-0 special case.

## Risks and open questions

1. **Kernel reduction speed for polynomial equality.** The
   `decide +kernel` check on `k • permA = L * U` has to compute
   polynomial products and compare them entry-wise. For an 8×8 matrix
   of degree-1 entries (the char-poly case), each entry of `L * U` is
   a sum of ≤ 8 products of degree-1 polynomials, so degree ≤ 2 and
   ≤ 8 monomials. Manageable but not free — needs benchmarking before
   committing to ℤ[X] as the witness representation.

2. **`DecidableEq (Polynomial ℤ)`.** Mathlib provides this, but the
   instance goes through `Finsupp.decidableEq` which iterates over the
   support. Whether this kernel-reduces fast enough is the open
   question that decides feasibility. If it doesn't, fallback is to
   represent matrix entries as `List ℤ` (coefficient lists) inside the
   witness and ship a one-shot lemma `coeffsEq → polyEq`.

3. **Meta-side rational function arithmetic.** Need `add`, `mul`, `div`,
   plus a normaliser that strips a common polynomial factor (so
   intermediate fractions don't blow up). Polynomial GCD over ℤ[X]
   (or over ℚ[X] then clear denominators) is standard but non-trivial
   to implement carefully.

4. **`Equiv.Perm.sign σ` cost on polynomial witnesses.** We confirmed
   it kernel-reduces fast enough for n=8 over ℤ. For ℤ[X] the matrix
   ops dominate, so sign should remain cheap. Re-benchmark anyway.

5. **Generic `det_of_smul_det` requirement.** Currently typed at ℤ.
   Generalising to any integral domain (or `NoZeroDivisors`) is a
   trivial edit but worth doing in milestone 1 to enable the new
   instances.

## Milestones

Each milestone is a working, committable state.

### Milestone 0 — design + Mathlib scout

* Confirm `Matrix.det_of_lowerTriangular`,
  `Matrix.det_of_upperTriangular`, `Matrix.det_permute`,
  `Matrix.det_smul`, `Matrix.det_mul` all hold in `CommRing` (they do —
  verify).
* Confirm `DecidableEq (Polynomial ℤ)` exists.
* Decide on the meta representation of `ℚ(X)`: probably
  `(num : List Int, den : List Int)` with `den` monic non-zero, both in
  reduced form.
* Update this plan with the chosen names and signatures.

**Demonstration:** plan updated; no code changes.

### Milestone 1 — generalise the Lean side

* Generalise `det_of_smul_det`, `intDetWitness`,
  `intDetWitnessPerm`, and their lemmas from `ℤ` to a typeclass-bounded
  `R`. For the cancellation step we need `[CommRing R] [NoZeroDivisors R]`
  (or `IsDomain R`).
* Existing ℤ tests must still pass with no edits beyond import paths.

**Demonstration:** `IntDetSimprocTest.lean` builds unchanged. The
generalised lemmas are usable in `R = ℚ` and `R = ℤ[X]` via type
inference.

### Milestone 2 — ℚ matrices (smoke test for the generalisation)

A minimal, low-risk validation that the generalisation works before
diving into polynomial arithmetic.

* New file `RatDetSimproc.lean` mirroring `IntDetSimproc.lean` but for
  `Matrix (Fin n) (Fin n) ℚ`.
* Meta side is trivial: ℚ entries are already what `exactMinScaling`
  consumes — just skip the integer-lift step.
* No scaling is needed because ℚ is a field (`n_min = 1`), so the
  witness is even simpler than the ℤ case.

**Demonstration:** simproc closes `(!![1/2, 1; 1, 2] : Matrix _ _ ℚ).det = 0`
in one `simp only`. Catches any regressions in the generic plumbing
before they're entangled with polynomial bugs.

### Milestone 3 — `RatPoly` meta arithmetic

The substantive engineering chunk. Implement `(ℤ[X] / ℤ[X])`
arithmetic in meta — call the type `RatPoly`.

* `IntPoly := List Int` (coefficient list, low-to-high; `[]` ≡ 0).
* `RatPoly := { num : IntPoly, den : IntPoly }` with the invariant
  that `den` has positive leading coefficient and `gcd(num, den) = 1`.
* Operations: `add`, `sub`, `mul`, `div`, `neg`, `eq`, `normalize`.
* Polynomial GCD over ℤ[X]: implement either by going via ℚ[X] (clear
  denominators, run Euclidean algorithm, primitive-part normalise) or
  by subresultant pseudo-remainder. The former is shorter but produces
  larger intermediate values.
* `RatPoly.ofInt`, `RatPoly.X` (the indeterminate), `RatPoly.toIntPoly?`
  (returns `some` iff denominator is `1`).

**Demonstration:** unit tests via `#eval` showing arithmetic on
small polynomials matches hand calculations. `(X+1) * (X-1) =? X² - 1`,
`(X² + 1) / (X + 1)` returns the right `RatPoly` rep, etc.

### Milestone 4 — ℤ[X] determinant simproc

* New file `PolyDetSimproc.lean`.
* Reuse the existing pivoted LU algorithm in `LUMinScaling.lean`,
  parameterised over a meta arithmetic interface (or copy and
  specialise to `RatPoly`).
* `evalPolyMatrixExpr`: extract a `Matrix (Fin n) (Fin n) (Polynomial ℤ)`
  from an `Expr` into `List (List IntPoly)`. Likely uses
  `Lean.Meta.evalExpr` on a helper `toPolyLists` returning
  `List (List (List Int))` (each polynomial as its coefficient list).
* `matOfPolyList`, the analogue of `matOfList`, produces a
  kernel-computable polynomial matrix Expr from coefficient lists.
* The witness predicate is the generalised `intDetWitnessPerm` at
  `R = Polynomial ℤ`. Proof discharge via `mkDecideProof`.

**Demonstration:** `simp only [polyDetSimproc]` reduces
`!![X+1, 2; 3, X-1].det` to `X^2 - 7`, with `#print axioms` showing
only the standard three.

**Open:** if `DecidableEq (Polynomial ℤ)` is too slow under kernel
reduction, switch matrix-equality witness clauses to coefficient-list
equality (custom `polyMatEq` predicate) plus a pre-proved bridge
lemma.

### Milestone 5 — `Matrix.charpoly` entry point

The user-facing payoff.

* Tactic / simproc `intCharpolySimproc` matching
  `Matrix.charpoly A` for `A : Matrix (Fin n) (Fin n) ℤ`.
* Internally: rewrite `Matrix.charpoly A = (X • 1 - A.map C).det` (the
  Mathlib definition or an unfolding), then delegate to
  `polyDetSimproc`.
* The "matrix mapping" `A.map C` lifts ℤ entries to constant
  polynomials and `X • 1 - A.map C` produces a polynomial matrix —
  the simproc reduces its determinant.

**Demonstration:** `(E₈.charpoly : Polynomial ℤ) = …` reduces in one
`simp only [intCharpolySimproc]`. Compare against a precomputed
expansion to verify correctness.

### Milestone 6 — tests, benchmarks, axioms

* 2×2, 3×3, 4×4 char-poly examples with hand-verified answers.
* `E₈.charpoly` (8×8) — the headline benchmark. Cyclotomic-style
  factor structure makes this a satisfying demo.
* No-op cases: matrix over an unsupported ring; symbolic matrix.
* Confirm `#print axioms` is clean for all char-poly tests.
* Time the 8×8 case under default heartbeats; report in this plan if
  the polynomial-equality kernel reduction is the bottleneck.

## Out of scope

* PIDs other than `ℤ` and `ℤ[X]` (e.g. `ℤ[i]`, `F[X, Y]`). The
  generic Lean side will accept them but the meta arithmetic isn't
  written.
* Char poly of polynomial matrices (would need `ℤ[X][Y]` arithmetic —
  doable, not in this plan).
* Fraction-free Bareiss algorithm. We're keeping the LU + scaling
  approach for consistency with the integer simproc; switching is a
  separate decision once we have benchmarks.
* `Matrix.charpoly` over rings other than `ℤ`.

## Implementation order

1. Milestone 0 (design pass, ~30 min, no code).
2. Milestone 1 (generic Lean, ~1 hr).
3. Milestone 2 (ℚ simproc, ~2 hr) — sanity check + de-risk.
4. Milestone 3 (`RatPoly`, ~half day) — most likely to surface
   surprises; build standalone with `#eval` tests before integrating.
5. Milestone 4 (ℤ[X] simproc, ~half day, plus benchmarking).
6. Milestone 5 (charpoly entry, ~1-2 hr).
7. Milestone 6 (tests + write-up).

If milestone 3 reveals serious GCD/normalization complexity, fall back
to a "no normalization" representation (`RatPoly` without coprime
invariant) and accept polynomial blow-up — for n=8 the entries stay
small enough that this is probably fine.
