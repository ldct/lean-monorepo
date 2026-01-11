# Lean Monorepo

This repository is a grab bag of Lean-related materials. The directory layout is mostly organized by Lean toolchain/version (`v19/`, `v20/`, `v22/`, `v23-rc2/`, `v24/`), but the work itself clusters by topic.

## Outside the Lean projects

- `informal/`: PDF papers and notes referenced while exploring Lean topics.
- `tutorials/`: Notes, markdown write-ups, and tutorial materials (Simons/FPV folders and misc. Lean notes).

## Advent of Code

- `v19/LeanGT/AoC/`: Advent of Code solutions and parsing utilities (`day1.lean`, `day2.lean`, `Parsers.lean`, etc.).

## Analysis / Limits / Series

- `v19/LeanGT/Analysis/`: Limits, series, and convergence notes (monotone convergence, infinite sums, order limits, reindexing).
- `v20/playground/Playground/TendsTo.lean` and `v22/playground/Playground/TendsTo.lean`: smaller experiments with limits using absolute value bounds.

## Group Theory and Finite Groups

- `v19/LeanGT/GroupTheory/`: Dihedral groups, centers/centralizers, normalizers, and related computations.
- `v24/playground/Playground/Geometry/`: group-theoretic constructions (e.g., dihedralization, Frobenius groups, cyclic and dicyclic examples).
- `v24/playground/Playground/Geometry/SmallGroups/`: small-group enumeration and property evaluation modules, backed by helper scripts in `v24/playground/`.

## Geometry / Isometries / Finite Geometry

- `v20/playground/Playground/Geometry.lean`, `v22/playground/Playground/Geometry.lean`: exercises on permutations of `ℝ`, translations as a subgroup, and isometries as a subgroup of `Perm ℝ`.
- `v20/playground/Playground/RealIsometry.lean`, `v22/playground/Playground/RealIsometry.lean`: define real-line isometries `ℝ → ℝ`, show reflections/translations preserve distance, and build a monoid via composition.
- `v24/playground/Playground/RealIsometry.lean`: defines isometries of `ℝ³` (as `EuclideanSpace ℝ (Fin 3)`), including translations and orthogonal actions, with inverses and composition.
- `v24/playground/Playground/Geometry/FiniteGeometry*.lean`: finite geometry-focused work.

## Number Theory / Algebraic Structures

- `v20/playground/Playground/GaussianIntegers*.lean`, `v22/playground/Playground/GaussianIntegers*.lean`: Gaussian integer experiments.
- `v23-rc2/playground/Playground/Rational/`: dyadic/ZZ/ZN rational constructions.

## Linear Algebra / Topology / Misc. Math Experiments

- `v23-rc2/playground/Playground/LinearAlgebra/`: linear algebra scratch work.
- `v23-rc2/playground/Playground/Topology/`: topology scratch work.
- `v23-rc2/playground/Playground/NormNumI.lean`: norm/complex arithmetic simp experiments.
- `v24/playground/Playground/orthogonal.lean`, `v24/playground/Playground/ListsTest.lean`, `v24/playground/Playground/abc436_a.lean`: standalone experiments.

## Banach–Tarski and related experiments

- `v24/playground/Playground/banach_tarski_mwe*.lean`, `v24/playground/Playground/bt_2025.*`: Banach–Tarski work and notes.

## Aristotle test harness

- `v20/playground/AristotleTest_aristotle.lean`, `v22/playground/AristotleTest_aristotle.lean`, `v24/playground/Playground/ml_tests_aristotle.lean` and accompanying `aristotle.py` scripts.

## Where to start

If you are looking for Lean code, start in `v19/LeanGT/` for the most structured projects, or in `v24/playground/` for the most active sandbox and helper scripts.
