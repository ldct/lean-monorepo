# Chapter 2 Proof Status — Round 1

## Summary

- **Total declarations**: 39 (16 theorems, 20 defs, 3 lemmas)
- **Definitions (no proof needed)**: 20 — all present
- **Theorems/lemmas needing proofs**: 19
- **Proofs completed**: 14
- **Proofs with sorry**: 5 declarations (6 sorry instances, since Ch2_theorem_30 has 2)
- **Coverage check**: 100% (39/39 statements preserved)
- **Build status**: Compiles with no errors, 5 sorry warnings

## Completed Proofs

### Ch2_theorem_3 (COMPLETED — already proven)
Proposition 2.1: Units form a group, abelian if ring is commutative.
- Strategy: Direct application of `mul_one`, `one_mul`, `mul_inv_cancel`, `inv_mul_cancel`, `mul_assoc`, `mul_comm`

### Ch2_lemma_16 (COMPLETED — already proven)
Lemma 2.1: Irreducible elements are prime in a PID.
- Strategy: `exact Irreducible.prime ha`

### Ch2_theorem_17 (COMPLETED — already proven)
Proposition 2.3: Prime elements are irreducible in an integral domain.
- Strategy: `exact Prime.irreducible ha`

### Ch2_theorem_19 (COMPLETED — already proven)
Proposition 2.4: Irreducible elements are prime in a UFD.
- Strategy: `exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ha`

### Ch2_theorem_20 (COMPLETED — already proven)
Theorem 2.2: PIDs are UFDs.
- Strategy: `infer_instance`

### Ch2_theorem_21 (COMPLETED — proved this round)
Theorem 2.3: Fermat's two-square theorem.
- **Attempt 1:** Tried using only Mathlib's `Nat.Prime.sq_add_sq` for existence → existence works but uniqueness needs manual proof
- **Final strategy:** 
  - Existence: `Nat.Prime.sq_add_sq` from `Mathlib.NumberTheory.SumTwoSquares`
  - Uniqueness: Elementary proof using:
    - Product identity: `(ax-by)(ax+by) = p(a²-y²)` (proved by substituting `a²=p-b²`, `x²=p-y²`)
    - Primality of p gives `p | (ax-by)` or `p | (ax+by)`
    - Lagrange identity: `(ax-by)² + (ay+bx)² = p²` gives bounds `|ax-by| ≤ p`
    - Bound lemma: if `p | n` and `n² ≤ p²` then `n ∈ {0, ±p}`
    - Six subcases deriving `x² = a²` or `x² = b²` from each case
  - Required `set_option maxHeartbeats 800000` due to many `nlinarith` calls
  - Added import `Mathlib.NumberTheory.SumTwoSquares`

### Ch2_theorem_26 (COMPLETED — already proven)
Theorem 2.4: Maximal ideal iff quotient is a field.
- Strategy: `exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I`

### Ch2_theorem_27 (COMPLETED — already proven)
Theorem 2.5: Prime ideal iff quotient is an integral domain.
- Strategy: `exact (Ideal.Quotient.isDomain_iff_prime I).symm`

### Ch2_theorem_28 (COMPLETED — already proven)
Theorem 2.6: Maximal ideals are prime.
- Strategy: `exact hI.isPrime`

### Ch2_theorem_29 (COMPLETED — already proven)
Theorem 2.7: Maximal ideal of a field is zero.
- Strategy: Case split `Ideal.eq_bot_or_top`, then contradiction with `hI.ne_top`

### Ch2_lemma_33 (COMPLETED — already proven)
Zorn's Lemma formalization.
- Strategy: `zorn_le` with chain upper bound

### Ch2_lemma_34 (COMPLETED — already proven)
Union of chain of ideals is an ideal.
- Strategy: Direct construction of ideal from set `{x | ∃ J ∈ C, x ∈ J}` with chain ordering

### Ch2_theorem_35 (COMPLETED — already proven)
Proper ideal contained in maximal ideal.
- Strategy: `I.exists_le_maximal hI`

### Ch2_corollary_36 (COMPLETED — already proven)
Intersection of all prime ideals = nilradical.
- Strategy: `ext x; simp; rw [nilradical_eq_sInf]; simp`

## Partially Completed (with sorry)

### Ch2_theorem_30 (IN PROGRESS — 3/5 parts proven, 2 sorry)

**Parts proven:**
1. Fields ⊂ ED: norm function `if x = 0 then 0 else 1`, division by `b⁻¹ * a`
2. PID ⊂ UFD: `infer_instance`
3. ID ⊂ CRings: trivial existential

**Part with sorry (ED ⊂ PID):**
- Same instance diamond as Ch2_theorem_12 — see below

**Part with sorry (UFD ⊂ ID):**
- `UniqueFactorizationMonoid` does NOT imply `Nontrivial`
- The trivial ring is a UFD but not an integral domain
- Flagged as unfaithful statement

### Ch2_theorem_38 (IN PROGRESS — equivalence proven, existential sorry)

The equivalence relation part (first conjunct) is fully proven:
- Reflexivity, symmetry: trivial
- Transitivity: Using `mul_eq_zero` with no-zero-divisors hypothesis

**Existential part with sorry:**
- Universe mismatch: `∃ (L : Type*)` introduces universe `u_2`, but `Localization S : Type u_1`
- `IsLocalization.{u_1, u_1}` vs `IsLocalization.{u_1, u_2}`
- Flagged as unfaithful — the existential should use the same universe as R

### Ch2_theorem_39 (IN PROGRESS — equivalence proven, existential sorry)

The equivalence relation part (first conjunct) is fully proven:
- Reflexivity: witness `⟨1, S.one_mem⟩`
- Symmetry: `linear_combination -hs₃`
- Transitivity: witness `⟨t₁ * t₂ * s₂, ...⟩` with `linear_combination`

**Existential part with sorry:**
- Same universe issue as Ch2_theorem_38

## Unfaithful Statements (sorry required, documented)

### Ch2_theorem_5 (NOT PROVEN — unfaithful statement)

**Attempt 1:** Tried using Mathlib's `CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral` → requires `IsMulCentral` (central idempotent) and `CommSemiring`
**Attempt 2:** Tried CRT approach with `Ideal.quotientInfEquivQuotientProd` → requires `CommRing`, statement has only `Ring`
**Attempt 3:** Tried direct construction with subtypes → fails for non-central idempotents

**Key blocker:** The statement claims R ≃+* A × B for ANY idempotent in ANY ring. This is FALSE for non-central idempotents. Counterexample: M₂(k) with e = diag(1,0).

### Ch2_theorem_12 (NOT PROVEN — instance diamond)

**Attempt 1:** `inferInstance` → failed: can't synthesize `IsPrincipalIdealRing R` (two CommRing instances)
**Attempt 2:** `exact @EuclideanDomain.to_principal_ideal_domain R _` → type mismatch between CommRing instances
**Attempt 3:** `convert @EuclideanDomain.to_principal_ideal_domain R _` → leaves unsolvable goal `inst✝² = inst✝.toCommRing`
**Attempt 4:** Manual proof construction → `EuclideanDomain.div_add_mod` uses wrong ring operations

**Key blocker:** `[CommRing R]` and `[EuclideanDomain R]` create two distinct CommRing instances. The `IsPrincipalIdealRing R` uses the given CommRing but Mathlib's instance uses the ED's CommRing.
