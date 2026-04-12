# Chapter 1 Proof Verification Results

**File Verified:** /root/for-claude/lean-monorepo/v29/playground/Playground/pdf_to_lean_workdir/lean_formalization_output/Formalization/ch1.lean

---

## 1. Build Verification
**Status:** PASS

Build completed successfully (3107 jobs). The only warnings are long-line style linter warnings in comment blocks (lines 16, 25, 32, 45, 49, 64, 76, 101, 112, 119, 122, 126, 138, 143, 155), which are non-functional and do not affect correctness.

---

## 2. Sorry and Axiom Check
### 2a. Sorry Check
**Status:** PASS
**Occurrences found:** 0

### 2b. Axiom Check
**Status:** PASS
**Occurrences found:** 0

---

## 3. Coverage Check (Statement Preservation)
**Status:** PASS

All 11 statements (2 theorems, 9 definitions) found exactly once. Coverage: 100.0%.

---

## 4. Adjacency Check
**Status:** FAIL
**Violations found:** 1

**Violation:** Comment block at lines 10-18 (Definition 1.1) has `universe u` on line 19 between the closing `-/` and the declaration `Ch1_def_1` at line 20. Only blank lines are permitted between a LaTeX quote comment block and its declaration.

**Fix:** Move `universe u` before the comment block (e.g., to line 9, before the `/-Exact quote...` block).

---

## 5. Semantic Equivalence Check (Mathlib4 Definitions)

### Key Mathlib concepts verified:

1. **`Equiv.Perm α`** (used in Ch1_def_1, Ch1_def_10, Ch1_theorem_11): Defined in `Mathlib.Logic.Equiv.Defs` as the type of bijections from `α` to itself. This is the standard permutation group, matching the textbook's "group of permutations of S". **CORRECT.**

2. **`MulAction.toPermHom G G`** (used in Ch1_theorem_11 — Cayley's theorem): Defined in `Mathlib.Algebra.Group.Action.End` with type `(G : Type) (α : Type) [Group G] [MulAction G α] : G →* Equiv.Perm α`. It sends each `g : G` to the permutation given by left multiplication by `g`. When applied as `MulAction.toPermHom G G`, this is the Cayley embedding of `G` into `Perm(G)`. **CORRECT.**

3. **`MulAction.toPerm_injective`** (used in Ch1_theorem_11): Defined in `Mathlib.Algebra.Group.Action.Basic` with type `[FaithfulSMul α β] : Function.Injective MulAction.toPerm`. The left regular action of `G` on itself is faithful (if `g * x = x` for all `x`, then `g = 1`), so `FaithfulSMul G G` holds automatically. This gives the injectivity needed for Cayley's theorem. **CORRECT.**

4. **`G →* H` (MonoidHom)** (used in Ch1_theorem_5, Ch1_def_6, Ch1_def_7): Standard Mathlib bundled group homomorphism. `map_one` and `map_inv` are standard lemmas for MonoidHom. **CORRECT.**

5. **`G ≃* G` (MulEquiv)** (used in Ch1_def_8 — Automorphism): A `MulEquiv` is a bijective group homomorphism, exactly matching "isomorphism and endomorphism" (bijective homomorphism from G to G). **CORRECT.**

6. **`Function.Bijective f`** (used in Ch1_def_6 — Isomorphism): Standard Mathlib definition of bijectivity (injective and surjective). Matches textbook's "bijection". **CORRECT.**

**Semantic Status:** PASS — All Mathlib definitions are semantically consistent with the textbook's mathematical intent.

### Suggested Mathlib4 files for reference

The following Mathlib4 files contain definitions and lemmas directly relevant to Chapter 1's formalization and could assist with future proof development:

- `Mathlib.Algebra.Group.Action.End` — `MulAction.toPermHom`, Cayley embedding
- `Mathlib.Algebra.Group.Action.Basic` — `MulAction.toPerm_injective`, faithful actions
- `Mathlib.GroupTheory.Perm.Basic` — `Equiv.Perm` group structure, permutation operations
- `Mathlib.GroupTheory.Perm.Subgroup` — `Equiv.Perm.subgroupOfMulAction` (Cayley's theorem as `G ≃* ↥(MulAction.toPermHom G H).range`)
- `Mathlib.Algebra.Group.Subgroup.Defs` — `Subgroup` bundled structure (alternative to Ch1_def_3's set-based predicate)
- `Mathlib.Algebra.Group.Units.Equiv` — `MulEquiv` (automorphisms)
- `Mathlib.GroupTheory.GroupAction.Defs` — `MulAction` typeclass (alternative to Ch1_def_9's manual predicate)

---

## Summary
**Build:** PASS
**Sorry-free:** PASS
**Axiom-free:** PASS
**Coverage:** PASS
**Adjacency:** FAIL (1 violation: `universe u` between comment block and declaration)
**Semantic Equivalence:** PASS

### Overall Verdict: FAIL

The single failure is the adjacency violation: `universe u` on line 19 appears between the LaTeX quote comment block (lines 10-18) and the `Ch1_def_1` declaration (line 20). Moving `universe u` above the comment block will resolve this issue.
