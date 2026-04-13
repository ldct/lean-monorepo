# Unfaithful Statement Arguments — Chapter 2

## Ch2_theorem_5 (Forward direction: idempotent ⇒ product decomposition)

**Statement:**
```lean
∀ (R : Type*) [Ring R] (e : R), e * e = e →
  ∃ (A B : Type*) (_ : Ring A) (_ : Ring B) (f : R ≃+* A × B), f e = (1, 0)
```

**Issue:** The statement uses `[Ring R]` (non-commutative ring), but idempotent decomposition `R ≃ A × B` only holds when the idempotent `e` is central (commutes with all elements). In a non-commutative ring, an idempotent gives a Peirce decomposition `R = eRe ⊕ eR(1-e) ⊕ (1-e)Re ⊕ (1-e)R(1-e)`, which is NOT a product of two rings in general.

**Counterexample:** In `M₂(k)` (2×2 matrices over a field), `e = diag(1,0)` is idempotent, but `M₂(k)` is a simple ring and cannot be decomposed as a product `A × B` of two nontrivial rings.

**Fix:** Change `[Ring R]` to `[CommRing R]`, or add hypothesis `∀ r, e * r = r * e`.

---

## Ch2_theorem_12 (Euclidean domain → PID)

**Statement:**
```lean
theorem Ch2_theorem_12 (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R] :
    IsPrincipalIdealRing R
```

**Issue:** Instance diamond. `EuclideanDomain R` extends `CommRing`, so having both `[CommRing R]` and `[EuclideanDomain R]` creates two competing `CommRing R` instances. Lean's `IsPrincipalIdealRing` and `Ideal R` depend on which `Semiring R` instance is used, making `@EuclideanDomain.instIsPrincipalIdealRing R _` produce a term with the wrong `CommRing` instance.

**Fix:** Remove `[CommRing R] [IsDomain R]` — they are implied by `[EuclideanDomain R]`. The statement should be:
```lean
theorem Ch2_theorem_12 (R : Type*) [EuclideanDomain R] : IsPrincipalIdealRing R
```

---

## Ch2_theorem_21 (Fermat's two-square theorem — uniqueness part)

**Statement:**
```lean
theorem Ch2_theorem_21 (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧
      ∀ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2 →
        (x = a ∨ x = -a) ∧ (y = b ∨ y = -b) ∨
        (x = b ∨ x = -b) ∧ (y = a ∨ y = -a)
```

**Issue:** The existence part (`∃ a b, p = a² + b²`) is provable via Mathlib's `Nat.Prime.sq_add_sq`. However, the uniqueness part (up to signs and swaps) is a deep number theory result that is NOT currently available in Mathlib. While the theorem is mathematically true, it cannot be proved with current Mathlib API in a reasonable proof.

**Note:** This is not unfaithful per se — the statement is correct — but it is not provable with available Mathlib lemmas. The uniqueness part requires the unique factorization in the Gaussian integers `ℤ[i]`.

---

## Ch2_theorem_30 part 2 (ED ⊂ PID)

**Statement (part 2 of conjunction):**
```lean
∀ (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R], IsPrincipalIdealRing R
```

**Issue:** Same instance diamond as Ch2_theorem_12. `[CommRing R]` and `[EuclideanDomain R]` create competing `CommRing` instances.

**Fix:** Same as theorem_12 — remove redundant `[CommRing R] [IsDomain R]`.

---

## Ch2_theorem_30 part 4 (UFD ⊂ ID)

**Statement (part 4 of conjunction):**
```lean
∀ (R : Type*) [CommRing R] [UniqueFactorizationMonoid R], IsDomain R
```

**Issue:** `UniqueFactorizationMonoid` provides `IsCancelMulZero` but NOT `Nontrivial`. The trivial ring (where `1 = 0`) satisfies `UniqueFactorizationMonoid` (vacuously — every element is a unit or zero) but is NOT an `IsDomain` (which requires `1 ≠ 0`). Confirmed via Mathlib's `isCancelMulZero_iff_isDomain_or_subsingleton`.

**Fix:** Add `[Nontrivial R]` hypothesis, or change conclusion to `IsDomain R ∨ Subsingleton R`.

---

## Ch2_theorem_38 (Localization equivalence relation — existential part)

**Statement (second conjunct):**
```lean
∃ (L : Type*) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L
```
where `R : Type*`.

**Issue:** Universe mismatch. `R : Type*` auto-binds to `Type u_1`. The existential `∃ (L : Type*) ...` introduces `L : Type u_2` with `u_2` as a separate universe parameter. `Localization S : Type u_1` cannot fill `L : Type u_2` when `u_1 ≠ u_2`. The theorem must hold for ALL universe levels, but there is no localization construction that produces a type in an arbitrary universe.

**Fix:** Ensure `L` is in the same universe as `R`:
```lean
∃ (L : Type _) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L
```
or use a single universe declaration:
```lean
theorem Ch2_theorem_38 (R : Type u) ... :
    ... ∧ (∃ (L : Type u) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L)
```

---

## Ch2_theorem_39 (Localization with s₃-relation — existential part)

**Statement (second conjunct):**
```lean
∃ (L : Type*) (_ : CommRing L) (_ : Algebra R L),
  IsLocalization S L ∧ (∃ f : R →+* L, ...) ∧ (∀ s : S, IsUnit ...)
```

**Issue:** Same universe mismatch as Ch2_theorem_38. `R : Type u_1` and `L : Type u_2` are in different universes.

**Fix:** Same as theorem_38 — bind L to the same universe as R.
