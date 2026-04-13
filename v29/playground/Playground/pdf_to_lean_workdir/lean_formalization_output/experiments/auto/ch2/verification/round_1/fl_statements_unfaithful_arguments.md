# Unfaithful Statements in Chapter 2

## Ch2_theorem_5 (Proposition 2.2 — Idempotent Decomposition)

**LaTeX quote:**
```
\begin{theorem}[Proposition 2.2]
More generally, for a ring R, suppose e ∈ R is idempotent. Then we have:
R = eR ⊕ (1 - e)R
both of which are rings. Conversely, in A × B, (1, 0) is idempotent.
\end{theorem}
```

**Current Lean statement:**
```lean
theorem Ch2_theorem_5 :
    (∀ (R : Type*) [Ring R] (e : R), e * e = e →
      ∃ (A B : Type*) (_ : Ring A) (_ : Ring B) (f : R ≃+* A × B), f e = (1, 0)) ∧
    (∀ (A B : Type*) [Ring A] [Ring B],
      ((1 : A), (0 : B)) * ((1 : A), (0 : B)) = ((1 : A), (0 : B)))
```

**Issue:** The forward direction claims that for ANY ring R and ANY idempotent e, there exists a ring isomorphism R ≃+* A × B sending e to (1, 0). This is FALSE for non-central idempotents in non-commutative rings.

**Counterexample:** R = M₂(k) (2×2 matrices over a field k), e = diag(1,0). Then e is idempotent but not central. M₂(k) is a simple ring (no nontrivial two-sided ideals), so it cannot decompose as a ring product A × B. Moreover, if f : R ≃+* A × B existed with f(e) = (1,0), then e would need to be central (since (1,0) is central in A × B), which it is not.

**Fix:** Either:
1. Add `[CommRing R]` instead of `[Ring R]` (the decomposition works for commutative rings)
2. Add `IsMulCentral e` as a hypothesis (for central idempotents in non-commutative rings)
3. Change to a module decomposition: `R ≃ₗ[ℤ] eR × (1-e)R` as additive groups

---

## Ch2_theorem_12 (Theorem 2.1 — Euclidean Domains are PIDs)

**LaTeX quote:**
```
\begin{theorem}[Theorem 2.1]
All Euclidean domains are PIDs.
\end{theorem}
```

**Current Lean statement:**
```lean
theorem Ch2_theorem_12 (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R] :
    IsPrincipalIdealRing R
```

**Issue:** The statement has both `[CommRing R]` and `[EuclideanDomain R]`. Since `EuclideanDomain` extends `CommRing`, this creates an instance diamond: there are TWO `CommRing R` instances. The `IsPrincipalIdealRing R` in the goal uses the given `[CommRing R]`, while Mathlib's `EuclideanDomain.to_principal_ideal_domain` provides `IsPrincipalIdealRing` using the `EuclideanDomain`'s `CommRing`. These types are not definitionally equal, making the goal unprovable with `convert` leaving the unsolvable goal `inst✝² = inst✝.toCommRing`.

**Fix:** Remove `[CommRing R]` and optionally `[IsDomain R]` (both are provided by `[EuclideanDomain R]`):
```lean
theorem Ch2_theorem_12 (R : Type*) [EuclideanDomain R] : IsPrincipalIdealRing R
```

---

## Ch2_theorem_30 (Proposition 2.5 — Chain of Inclusions), ED ⊂ PID part

Same instance diamond issue as Ch2_theorem_12. The statement:
```lean
(∀ (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R], IsPrincipalIdealRing R)
```
has both `[CommRing R]` and `[EuclideanDomain R]`.

**Fix:** Remove `[CommRing R] [IsDomain R]`:
```lean
(∀ (R : Type*) [EuclideanDomain R], IsPrincipalIdealRing R)
```

---

## Ch2_theorem_30 (Proposition 2.5 — Chain of Inclusions), UFD ⊂ ID part

**Current Lean statement (this part):**
```lean
(∀ (R : Type*) [CommRing R] [UniqueFactorizationMonoid R], IsDomain R)
```

**Issue:** `UniqueFactorizationMonoid` does NOT imply `Nontrivial`. In Mathlib, `UniqueFactorizationMonoid` extends `IsCancelMulZero` (which gives `NoZeroDivisors`), but NOT `Nontrivial`. The trivial ring `{0}` satisfies `UniqueFactorizationMonoid` (vacuously) but not `IsDomain` (which requires `Nontrivial`, i.e., `0 ≠ 1`).

**Fix:** Add `[Nontrivial R]`:
```lean
(∀ (R : Type*) [CommRing R] [Nontrivial R] [UniqueFactorizationMonoid R], IsDomain R)
```

Or change to `[IsDomain R]` and use the Mathlib pattern where `IsDomain` and `UniqueFactorizationMonoid` are both assumed.

---

## Ch2_theorem_38 (Proposition 2.6 — Localization Existence)

**Current Lean statement (second conjunct):**
```lean
(∃ (L : Type*) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L)
```

**Issue:** The `∃ (L : Type*)` introduces a fresh auto-bound universe variable `u_2`, while `R : Type*` uses `u_1`. The only known localization `Localization S` lives at `Type u_1` (same universe as `R`). The theorem requires a witness at `Type u_2` for ALL values of `u_2`, but there's no way to construct `IsLocalization S L` for `L` at an arbitrary universe without `ULift` support for `IsLocalization` (which doesn't exist in Mathlib).

**Fix:** Constrain the universe of `L` to match `R`, e.g.:
```lean
∃ (L : Type _) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L
```
Or more explicitly, make the theorem use a single universe variable.

---

## Ch2_theorem_39 (Proposition 2.7 — Localization with s₃-relation)

Same universe issue as Ch2_theorem_38. The existential `∃ (L : Type*)` uses a different universe than `R`.
