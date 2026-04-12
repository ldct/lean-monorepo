# Statement Change History — Chapter 1, Round 1

## Ch1_def_1 (Definition 1.1, Concrete group) — ACCEPTED

**Date:** 2026-04-12

**Issue:** Universe bug. `Ch1_def_1` used `Type*` for both `G` and `S` (in the existential), creating two independent universe parameters `u_1` and `u_2`. This made `Ch1_theorem_11` (Cayley's theorem) unprovable because the natural witness `S = G` lives in `Type u_1`, not `Type u_2`.

**Change applied:**
- Added `universe u` declaration before the definition.
- Changed `G : Type*` to `G : Type u`.
- Changed `S : Type*` to `S : Type u`.

**Before:**
```lean
def Ch1_def_1 (G : Type*) [Group G] : Prop :=
  ∃ (S : Type*), ∃ (f : G →* Equiv.Perm S), Function.Injective f
```

**After:**
```lean
universe u
def Ch1_def_1 (G : Type u) [Group G] : Prop :=
  ∃ (S : Type u), ∃ (f : G →* Equiv.Perm S), Function.Injective f
```

**Justification:** The LaTeX definition says "the set of symmetries of something" with no universe constraint. In standard mathematics there are no universe levels. Using the same universe for `G` and `S` is the standard, faithful formalization (consistent with Mathlib's approach). The two-universe version is strictly stronger than what the mathematical definition requires and makes a valid theorem unprovable.
