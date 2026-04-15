# Plan: extend `intDetSimproc` to matrices requiring pivoting

## Goal

Lift the v1 restriction that `exactMinScaling` must succeed without
permutations. After this work, the simproc handles any non-singular
integer matrix (up to 8×8) by computing a partial pivoted LU
decomposition `P A = L U` and emitting

```
det A = sign(P)⁻¹ · det L · det U / n_min^n
```

with `sign(P) ∈ {+1, -1}`.

## Math

For a permutation matrix `P` corresponding to permutation `σ`:

```
det(P · A) = det(P) · det(A) = ε(σ) · det(A)
```

where `ε(σ) = ±1` is the signature. Combined with the existing scaled-LU
identity:

```
ε(σ) · n_min^n · det(A) = det(L_int) · det(U_int)
det(A) = ε(σ) · det(L_int) · det(U_int) / n_min^n
        = (sign as int) · prod-of-diagonals / n_min^n
```

The kernel-decidable witness becomes: `P A = (perm rows of A by σ)`,
`k · σ•A = L * U`, `det(P) = ε`, plus the existing triangularity and
arithmetic obligations.

## Representation choices

A few decisions to make up front (covered in milestone 0):

1. **Permutation as `List Nat` vs `Equiv.Perm (Fin n)`.** The metaprogram
   side is easier with `List Nat` (a row-order); the Lean side prefers
   `Equiv.Perm` for `Matrix.det_permute` / `Equiv.Perm.sign`. Bridge
   with a helper `permOfList : List Nat → Equiv.Perm (Fin n)` that
   builds the permutation by indexing.
2. **How to apply σ to A.** Either physically permute rows in meta and
   prove `σ • A = permA` (cleaner), or keep `σ` symbolic in the witness.
   Lean side: physical is simpler — emit `permA` as a `matOfList` and
   the only new witness clause is `σ • A = permA`.
3. **Where to compute the sign.** In meta, count inversions of σ; emit
   `ε : ℤ ∈ {1, -1}` as a literal. The witness then carries
   `Equiv.Perm.sign σ = ε` (decidable because `σ` is concrete).

## Modifying `LUMinScaling.lean`

`luDecompose` and `exactMinScaling` need to return permutation info.
Either change them in place (preferred — they're not used elsewhere) or
add `luDecomposeWithPivot` / `exactMinScalingWithPivot` alongside.

New `LUResult`:

```
structure LUResult where
  L : QMat
  U : QMat
  perm : List Nat   -- σ : i ↦ perm[i] ; identity = [0,1,…,n-1]
  ok : Bool         -- false only if matrix is singular
```

Algorithm change in `luDecompose`:

* At step `k`, look for the first `i ≥ k` with `U'.get i k ≠ 0`.
* If none → `ok := false` (matrix is singular).
* Else, swap rows `k` and `i` in the working `A`, in `L`'s columns
  `0..k-1` (the already-computed part), and record the swap in `perm`.

`exactMinScaling` is essentially unchanged; it just propagates the
`perm` field.

## Lean-side additions

In `IntDetSimproc.lean`:

```
def applyPerm (n : Nat) (perm : List Nat) (rows : List (List Int))
    : List (List Int) :=
  (List.range n).map fun i => rows.getD (perm.getD i 0) []

def signOfPerm (perm : List Nat) : Int :=
  -- count inversions, return (-1)^inv
  ...
```

New witness predicate:

```
abbrev intDetWitnessPerm {n : ℕ} (A L U permA : Matrix (Fin n) (Fin n) ℤ)
    (σ : Equiv.Perm (Fin n)) (ε k d detL detU : ℤ) : Prop :=
  k ≠ 0 ∧
  ε * ε = 1 ∧                    -- ε ∈ {±1}
  Equiv.Perm.sign σ = ε ∧        -- (Int.cast (sign σ) = ε)
  k • permA = L * U ∧
  (∀ i j : Fin n, permA i j = A (σ i) j) ∧
  triangularity-of-L ∧
  triangularity-of-U ∧
  ∏ diag L = detL ∧
  ∏ diag U = detU ∧
  ε * (detL * detU) = k ^ n * d
```

Companion lemma `det_eq_of_witnessPerm` does:

```
det(A) = sign(σ⁻¹) · det(σ • A)             -- Matrix.det_permute or similar
       = ε · (det(L * U)) / k^n              -- via det_of_smul_det
       = ε · detL · detU / k^n               -- triangularity
       = d                                    -- by harith
```

Need a Mathlib lemma like `Matrix.det_submatrix_equiv_self` or
`Matrix.det_permute`. Search-step: confirm exact name and direction
before milestone 2.

## Milestones

### Milestone 0 — design + Mathlib lemma scout

* Pick the representation choices above.
* Search Mathlib (leanexplore) for the canonical lemma relating
  `det A`, `det (A.submatrix σ id)`, and `Equiv.Perm.sign σ`. Likely
  candidates: `Matrix.det_permute_row`, `Matrix.det_submatrix_equiv_self`.
  Record the chosen lemma + its exact signature in this plan.
* Decide whether `luDecompose` is modified in place or copied.

**Demonstration:** plan updated; no code changes yet.

### Milestone 1 — pivoted `luDecompose` and `exactMinScaling`

* Implement row-swap pivoting in `luDecompose`.
* Extend `LUResult` and `MinScalingResult` with `perm : List Nat`.
* `#eval` smoke test: a matrix that needed `none` in v1 (e.g.
  `!![0, 1; 1, 0]`) now returns a result with `perm = [1, 0]`.
* Existing `IntDetSimprocTest` still passes (the no-pivot path produces
  `perm = [0, 1, …, n-1]`).

**Demonstration:** `#eval exactMinScaling (mkMatrix [[0,1],[1,0]])`
returns `some { perm := [1, 0], … }`.

### Milestone 2 — Lean-side helpers

* `applyPerm`, `signOfPerm`, `permOfList`.
* `intDetWitnessPerm` predicate + its `Decidable` instance (works
  automatically for `abbrev`).
* `det_eq_of_witnessPerm` lemma, proved by hand using the Mathlib lemma
  identified in milestone 0.

**Demonstration:** a hand-written instance of the new lemma proves
`(!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℤ).det = -1` without invoking the
simproc — confirms the lemma plumbing is correct.

### Milestone 3 — wire the simproc

* In `intDetSimproc`, when `data.perm ≠ identity`:
  * Build `permA` rows in meta.
  * Build `σ : Equiv.Perm (Fin n)` Expr via `permOfList`.
  * Compute `ε` and `d = ε · detL · detU / k^n`.
  * Build `intDetWitnessPerm` and discharge with `mkDecideProof`.
  * Apply `det_eq_of_witnessPerm`.
* When `data.perm = identity`, keep the existing fast path
  (`intDetWitness` + `det_eq_of_witness`) — avoids paying for the
  permutation Decidable check.

**Demonstration:** `IntDetSimprocTest`'s `NeedsPerm` case now closes
with one `simp only [intDetSimproc]` instead of `decide`.

### Milestone 4 — tests + benchmarking

* Promote the v1 no-op tests (`Sing`, `NeedsPerm`) to positive tests
  where applicable. `Sing` stays a no-op (genuinely singular).
* Add a 4×4 matrix that needs two row swaps.
* Add an 8×8 matrix that needs at least one swap (can construct by
  permuting rows of `E₈`).
* Verify `#print axioms` still shows only `propext, Classical.choice,
  Quot.sound` for the new tests.
* Time the 8×8 swap case; the kernel reduction of
  `Equiv.Perm.sign σ = ε` may be the bottleneck — if so, replace with a
  precomputed inversion-count witness.

**Demonstration:** test file builds under default heartbeats; axioms
clean.

## Risks / open questions

1. **`Equiv.Perm.sign` decidability cost.** The standard definition
   computes signature via cycle decomposition, which may be slow under
   kernel reduction even at n=8. Fallback: prove `sign σ = ε` via a
   custom lemma keyed on the inversion count of the row-list, which
   reduces faster.
2. **Permutation Expr construction.** Building an `Equiv.Perm (Fin n)`
   Expr is fiddly. Alternative: keep σ as `Fin n → Fin n` via
   `permOfList` and use `Matrix.det_submatrix_equiv_self` only after
   wrapping in `Equiv.ofBijective` (but bijectivity is then a side
   obligation). Probably easier to bake the permutation into the
   witness as the *list* and have the Lean lemma accept it that way:

   ```
   abbrev intDetWitnessPerm {n} (A L U : Matrix (Fin n) (Fin n) ℤ)
       (perm : List Nat) (ε k d detL detU : ℤ) : Prop := …
   ```

   Sign computed via `signOfList`, applied row-permutation expressed as
   `∀ i j, (L*U) i j = k * A ⟨perm.getD i.val 0, …⟩ j`. Avoids
   `Equiv.Perm` entirely. Strongly recommend this route — revisit in
   milestone 0.
3. **Singular detection.** With pivoting, the only failure mode of LU
   is genuine singularity. We could now *prove* `det A = 0` directly,
   but that's a separate feature — not in scope here.
4. **Should we generalise to LDU or rational-pivot strategies?** No —
   keep partial pivoting (row swaps only). Column swaps would change
   `det` by another sign and complicate the witness.
