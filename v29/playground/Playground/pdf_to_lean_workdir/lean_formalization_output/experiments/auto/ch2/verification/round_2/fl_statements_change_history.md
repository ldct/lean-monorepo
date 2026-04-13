# Chapter 2 — Statement Change History (Round 2)

## Ch2_theorem_5 — Universe Mismatch Fix

**Date:** 2026-04-13

**Decision:** ACCEPTED — Change applied.

**Issue:** The existential `∃ (A B : Type*) ...` in the forward direction introduced fresh universe parameters `u_2`, `u_3` independent of R's universe `u_1`. The natural witnesses (quotient rings of R) live in `Type u_1` and cannot fill existentials in different universes. This made the forward direction unprovable despite having a correct mathematical proof.

**Change applied:** Replaced `Type*` with `Type u` for R, A, B in both the forward and converse directions of `Ch2_theorem_5`, ensuring all types share the same universe variable `u` (already declared at file scope). Specifically:
- `∀ (R : Type*) [CommRing R] (e : R), ... ∃ (A B : Type*) ...` → `∀ (R : Type u) [CommRing R] (e : R), ... ∃ (A B : Type u) ...`
- `∀ (A B : Type*) [Ring A] [Ring B], ...` → `∀ (A B : Type u) [Ring A] [Ring B], ...`

**Justification:** This is a purely technical fix that does not change the mathematical content. The LaTeX statement quantifies over all rings without universe restrictions; using a single universe variable `u` is the standard Lean 4 idiom for faithfully encoding such statements while keeping the existential witnesses fillable.
