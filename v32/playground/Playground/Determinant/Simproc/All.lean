import Playground.Determinant.Simproc.LUMinScaling
import Playground.Determinant.Simproc.IntDetSimproc
import Playground.Determinant.Simproc.Test

/-!
# `intDetSimproc` — determinants of concrete integer matrices via scaled LU

A simproc that rewrites `Matrix.det A` to an integer literal for a concrete
`A : Matrix (Fin n) (Fin n) ℤ` (up to 8×8), using Gaussian elimination: it
computes a permuted, integer-scaled LU factorisation of the rational matrix
and recovers `det A` from `det L * det U = sign(σ) * n_min^n * det A`.

Handles non-singular matrices (with row pivoting) and singular matrices
(`det A = 0`) alike; the generated proofs use only the standard axioms.

## Modules
* `LUMinScaling` — the meta-level exact-minimal-scaling LU algorithm.
* `IntDetSimproc` — the `intDetSimproc` simproc and its witness lemmas.
* `Test` — worked examples (2×2 … 8×8 E₈, pivoting, singular).
-/
