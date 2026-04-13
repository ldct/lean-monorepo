# Faithfulness Statement Change History — Round 1

## Date: 2026-04-13

---

### Ch2_theorem_5 (Proposition 2.2 — Idempotent Decomposition)

**Decision: ACCEPTED — Change applied.**

**Reason:** The analysis is mathematically correct. The current statement claims that for ANY ring R and ANY idempotent e, there exists a ring isomorphism R ≃+* A × B sending e to (1,0). This is false for non-central idempotents in non-commutative rings (e.g., e = diag(1,0) in M₂(k)). The element (1,0) is central in A × B, so f(e) = (1,0) forces e to be central. The textbook's decomposition R = eR ⊕ (1-e)R as a ring product implicitly assumes commutativity.

**Change:** `[Ring R]` → `[CommRing R]` in the forward direction.

---

### Ch2_theorem_12 (Theorem 2.1 — Euclidean Domains are PIDs)

**Decision: ACCEPTED — Change applied.**

**Reason:** The analysis is correct. `EuclideanDomain` in Mathlib extends `CommRing`, so having both `[CommRing R]` and `[EuclideanDomain R]` creates two distinct `CommRing` instances (an instance diamond). This makes the goal `IsPrincipalIdealRing R` unprovable because the `IsPrincipalIdealRing` synthesized via `EuclideanDomain` uses a different `CommRing` instance than the one in scope.

**Change:** Removed `[CommRing R] [IsDomain R]`, keeping only `[EuclideanDomain R]`.

---

### Ch2_theorem_30 (Proposition 2.5 — Chain of Inclusions, ED ⊂ PID part)

**Decision: ACCEPTED — Change applied.**

**Reason:** Same instance diamond as Ch2_theorem_12. `[CommRing R] [IsDomain R]` are redundant with `[EuclideanDomain R]` and create conflicting instances.

**Change:** `∀ (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R]` → `∀ (R : Type*) [EuclideanDomain R]`.

---

### Ch2_theorem_30 (Proposition 2.5 — Chain of Inclusions, UFD ⊂ ID part)

**Decision: ACCEPTED — Change applied.**

**Reason:** The analysis is correct. In Mathlib, `UniqueFactorizationMonoid` does not extend `Nontrivial`. The trivial ring `{0}` satisfies `UniqueFactorizationMonoid` vacuously but fails `IsDomain` (which requires `0 ≠ 1`, i.e., `Nontrivial`). Adding `[Nontrivial R]` makes the statement provable and faithful to the textbook's implicit assumption that rings in the chain are nontrivial.

**Change:** Added `[Nontrivial R]` to the UFD ⊂ ID conjunct.

---

### Ch2_theorem_38 (Proposition 2.6 — Localization Existence)

**Decision: ACCEPTED — Change applied.**

**Reason:** The analysis is correct. `R : Type*` auto-binds to universe `u_1`, while `∃ (L : Type*)` introduces a fresh universe `u_2`. The existential must be witnessed for ALL values of `u_2`, but `Localization S` lives in `Type u_1`. Without universe polymorphic `ULift` support for `IsLocalization`, this is unprovable. Pinning both to the same explicit universe `u` resolves this.

**Change:** `R : Type*` → `R : Type u`, `∃ (L : Type*)` → `∃ (L : Type u)`.

---

### Ch2_theorem_39 (Proposition 2.7 — Localization with s₃-relation)

**Decision: ACCEPTED — Change applied.**

**Reason:** Same universe issue as Ch2_theorem_38. The existential `∃ (L : Type*)` uses a different universe than `R`, making the witness `Localization S` inapplicable.

**Change:** `R : Type*` → `R : Type u`, `∃ (L : Type*)` → `∃ (L : Type u)`.

---
