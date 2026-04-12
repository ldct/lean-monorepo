# Chapter 1 — Proof Status Log (Round 3)

## Summary
- Total theorems: 2
- Proved: 2 (Ch1_theorem_5, Ch1_theorem_11)
- Remaining sorry: 0
- Coverage check: 100% (11/11 statements preserved)
- lake build: PASS (no errors, no sorry warnings — only long-line linter warnings in comment blocks)

---

## Round 3 Changes

Fixed the adjacency violation identified in Round 2's verification:
- Moved `universe u` from line 19 (between the comment block and `Ch1_def_1` declaration) to before the comment block.
- This resolves the only remaining issue from Round 2.

---

## Ch1_theorem_5 (Proposition 1.1: Homomorphisms preserve inverses and identity) — COMPLETED (Round 1)

Already proved in Round 1 using `exact ⟨map_one f, fun g => map_inv f g⟩`. No changes needed in Round 2 or 3.

---

## Ch1_theorem_11 (Theorem 1.1: Cayley's theorem — every group is a concrete group) — COMPLETED (Round 2)

Proved in Round 2 using Cayley's theorem via left regular representation:
```lean
theorem Ch1_theorem_11 (G : Type*) [Group G] : Ch1_def_1 G := by
  refine ⟨G, MulAction.toPermHom G G, ?_⟩
  rw [MulAction.coe_toPermHom]
  exact MulAction.toPerm_injective
```
No changes needed in Round 3.

---

## Verification Results (Round 3)

- lake build: PASS (Build completed successfully, 3107 jobs)
- Sorry check: PASS (0 occurrences)
- Axiom check: PASS (0 occurrences)
- Coverage check: PASS (11/11 statements, 100%)
- Adjacency violation: FIXED (moved `universe u` before comment block)
