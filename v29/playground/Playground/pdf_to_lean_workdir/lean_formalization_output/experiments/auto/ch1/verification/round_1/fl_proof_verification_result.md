# Chapter 1 Proof Verification Results

**File Verified:** /root/for-claude/lean-monorepo/v29/playground/Playground/pdf_to_lean_workdir/lean_formalization_output/Formalization/ch1.lean

---

## 1. Build Verification
**Status:** PASS

`lake build` completed successfully (3107 jobs). The only warnings related to ch1.lean are:
- Style warnings about lines exceeding 100 characters (all in comment blocks / natural language descriptions, not in code)
- A `declaration uses 'sorry'` warning for `Ch1_theorem_11` at line 182

No compilation errors.

---

## 2. Sorry and Axiom Check

### 2a. Sorry Check
**Status:** FAIL
**Occurrences found:** 1

| Line | Location |
|------|----------|
| 183 | `Ch1_theorem_11` (Cayley's theorem: every abstract group is a concrete group) |

**Details:** The `sorry` is in `Ch1_theorem_11`, which states that every group `G` satisfies `Ch1_def_1 G` (i.e., is a concrete group). The proof attempts log (lines 148–171) documents a **universe polymorphism issue**: `Ch1_def_1` uses `∃ (S : Type*)`, which introduces a fresh universe variable `u_2` independent of `G`'s universe `u_1`. Cayley's theorem requires instantiating `S := G`, but `G : Type u_1` cannot unify with the expected `Type u_2`. This is a formalization-level issue in the definition's universe parameters, not a missing proof technique.

### 2b. Axiom Check
**Status:** PASS
**Occurrences found:** 0

No `axiom` declarations found.

---

## 3. Coverage Check (Statement Preservation)
**Status:** PASS

```
Coverage: 100.0%
Type            Total    Found  Missing  Duplicate
theorem             2        2        0          0
def                 9        9        0          0
TOTAL              11       11        0          0
RESULT: COMPLETE - All statements found exactly once!
```

All 11 declarations (2 theorems, 9 definitions) from the spec file are present exactly once.

---

## 4. Adjacency Check
**Status:** PASS
**Violations found:** 0

```
ADJACENCY: PASS - All comment blocks immediately followed by correctly named declarations
RESULT: COMPLETE - All statements found exactly once, all adjacent!
```

---

## 5. Semantic Equivalence Check (Mathlib4 Definitions)

### Definitions and types verified against Mathlib4 source:

| Formalization construct | Mathlib4 definition | Semantic match? |
|---|---|---|
| `Equiv.Perm S` | `(α : Sort u) : Sort (max 1 u)` — the type of bijections from α to itself | **Correct.** Represents permutations/symmetries of S as intended by the textbook. |
| `G →* Equiv.Perm S` (in `Ch1_def_1`) | `MonoidHom` — a structure for group homomorphisms preserving `*` and `1` | **Correct.** An injective group homomorphism into Perm(S) correctly captures "G is the set of symmetries of something." |
| `Function.Injective f` (in `Ch1_def_1`) | Standard definition: `∀ a b, f a = f b → a = b` | **Correct.** |
| `Function.Bijective f` (in `Ch1_def_6`) | Standard: injective and surjective | **Correct.** Matches "isomorphism iff bijection." |
| `G →* G` (in `Ch1_def_7`) | MonoidHom from G to G | **Correct.** Endomorphism = homomorphism with same domain and codomain. |
| `G ≃* G` (in `Ch1_def_8`) | `MulEquiv` — a bundled multiplicative equivalence (bijective `*`-preserving map) | **Correct.** Automorphism = isomorphism + endomorphism = bijective homomorphism G → G. Confirmed via `MulEquiv.map_inv` in `Mathlib.Algebra.Group.Equiv.Defs`. |
| `map_one f` and `map_inv f g` (in `Ch1_theorem_5`) | Standard Mathlib lemmas for `MonoidHom`: `f 1 = 1` and `f g⁻¹ = (f g)⁻¹` | **Correct.** Exactly "homomorphisms preserve identity and inverses." |
| `Ch1_def_9` (left action) | Custom definition with two axioms: `smul g (smul h s) = smul (g*h) s` and `smul 1 s = s` | **Correct.** Matches the textbook's Definition 1.8. Note: Mathlib's `MulAction` has the same two axioms (`mul_smul` and `one_smul`). |
| `Ch1_def_10` (G-set) | `∃ (_ : G →* Equiv.Perm S), True` | **Correct.** A G-set is a set S with a group homomorphism G → Perm(S), matching Definition 1.9. |

**Semantic check verdict:** All definitions and theorem statements are semantically faithful to the textbook's intent. No mismatches found.

### Mathlib4 suggestion for fixing the `sorry` in `Ch1_theorem_11` (Cayley's Theorem)

The key Mathlib result for Cayley's theorem is:

- **`Equiv.Perm.subgroupOfMulAction`** (in `Mathlib.GroupTheory.Perm.Subgroup`):
  ```
  (G : Type) (H : Type) [Group G] [MulAction G H] [FaithfulSMul G H] :
    G ≃* ↥(MulAction.toPermHom G H).range
  ```
  This is literally Cayley's theorem: every group G is isomorphic to a subgroup of the symmetric group.

- **`MulAction.toPermHom`** (in `Mathlib.Algebra.Group.Action.End`):
  ```
  (G : Type) (α : Type) [Group G] [MulAction G α] : G →* Equiv.Perm α
  ```
  This gives the canonical homomorphism from a group action. Using `G`'s left-multiplication action on itself (`Mul.toSMul`), this yields the Cayley embedding `G →* Perm G`.

**However**, the root cause of the `sorry` is a **universe mismatch** in `Ch1_def_1`: the definition `∃ (S : Type*), ∃ (f : G →* Equiv.Perm S), Function.Injective f` introduces a universe variable for `S` that is independent of `G`'s universe. To fix the proof, the definition `Ch1_def_1` would need to be changed to use the same universe for both `G` and `S` (e.g., `∃ (S : Type _), ...` with a universe annotation tying them together), or the theorem statement would need explicit universe annotations like `Ch1_theorem_11.{u, u}`.

---

## Summary
| Check | Status |
|-------|--------|
| **Build** | PASS |
| **Sorry-free** | FAIL (1 occurrence in `Ch1_theorem_11`) |
| **Axiom-free** | PASS |
| **Coverage** | PASS |
| **Adjacency** | PASS |
| **Semantic equivalence** | PASS |

### Overall Verdict: FAIL

**Reason:** One `sorry` remains in `Ch1_theorem_11` (Cayley's theorem). The proof is blocked by a universe polymorphism issue in the `Ch1_def_1` definition — the existential `∃ (S : Type*)` creates a universe variable independent of `G`'s universe, preventing the natural Cayley embedding (which uses `S := G`) from type-checking. The Mathlib lemma `Equiv.Perm.subgroupOfMulAction` provides the mathematical content needed, but the universe mismatch in the formalized statement must be resolved first.
