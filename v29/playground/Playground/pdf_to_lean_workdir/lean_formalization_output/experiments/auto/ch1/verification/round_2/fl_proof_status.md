# Chapter 1 — Proof Status Log (Round 2)

## Summary
- Total theorems: 2
- Proved: 2 (Ch1_theorem_5, Ch1_theorem_11)
- Remaining sorry: 0
- Coverage check: 100% (11/11 statements preserved)
- lake build: PASS (no errors, no sorry warnings)

---

## Ch1_theorem_5 (Proposition 1.1: Homomorphisms preserve inverses and identity) — COMPLETED (Round 1)

Already proved in Round 1 using `exact ⟨map_one f, fun g => map_inv f g⟩`. No changes needed.

---

## Ch1_theorem_11 (Theorem 1.1: Cayley's theorem — every group is a concrete group) — COMPLETED (Round 2)

### Round 1 analysis (INCORRECT):
Round 1 concluded this theorem was unprovable due to a universe bug, claiming `Ch1_def_1` had two independent universe parameters (u_1 for G, u_2 for S). This was **wrong**. The definition explicitly uses `universe u` and both `G : Type u` and `S : Type u` share the same universe variable.

The round 1 attempts all failed with "Type u_1 expected Type u_2" errors. This was likely due to either:
1. A different version of the file at that time (possibly using `Type*` instead of `Type u` for S)
2. A misunderstanding of the error messages

### Round 2 approach (SUCCESS):

**Attempt 1:** `exact ⟨G, MulAction.toPermHom G G, mul_left_cancel⟩`
→ Failed: `mul_left_cancel` has wrong type (needs `a * b = a * c → b = c`, not `Function.Injective`).

**Attempt 2:** Used Loogle to find the correct injectivity lemma:
- `MulAction.toPerm_injective` provides `Function.Injective MulAction.toPerm` given `FaithfulSMul G G`
- `MulAction.coe_toPermHom` shows `⇑(MulAction.toPermHom G α) = MulAction.toPerm`
- `instFaithfulSMul` provides `FaithfulSMul G G` for any `MulOneClass G` (which `Group G` implies)

Final proof:
```lean
theorem Ch1_theorem_11 (G : Type*) [Group G] : Ch1_def_1 G := by
  refine ⟨G, MulAction.toPermHom G G, ?_⟩
  rw [MulAction.coe_toPermHom]
  exact MulAction.toPerm_injective
```

Strategy: Cayley's theorem via left regular representation. The witness `S := G` works because `Ch1_def_1` uses the same universe `u` for both `G` and `S`. `MulAction.toPermHom G G` is the canonical homomorphism from the left multiplication action, and `MulAction.toPerm_injective` proves injectivity using the `FaithfulSMul G G` instance (auto-derived from the group structure).

- lake build: success (no errors, no sorry warnings for ch1)
- Coverage check: 11/11 statements preserved (100%)
- Helper lemmas added: none
