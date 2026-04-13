# Chapter 2 Proof Status — Round 2

## Summary

- **Total declarations**: 39 (16 theorems, 20 defs, 3 lemmas)
- **Definitions (no proof needed)**: 20 — all present
- **Theorems/lemmas needing proofs**: 19
- **Proofs completed**: 18
- **Proofs with sorry**: 1 (Ch2_theorem_5 forward direction — universe mismatch)
- **Coverage check**: 100% (39/39 statements preserved)
- **Build status**: Compiles with no errors, 1 sorry warning

## Improvements from Round 1 → Round 2

Round 1 had 6 sorry instances. Round 2 resolved 5 of them:

1. **Ch2_theorem_12** (ED → PID): ✅ Proved with `exact EuclideanDomain.to_principal_ideal_domain`
2. **Ch2_theorem_30 (ED ⊂ PID)**: ✅ Proved with `exact EuclideanDomain.to_principal_ideal_domain`
3. **Ch2_theorem_30 (UFD ⊂ ID)**: ✅ Proved using `isCancelMulZero_iff_noZeroDivisors.mp` to derive `NoZeroDivisors` from `UniqueFactorizationMonoid`
4. **Ch2_theorem_38 (localization existence)**: ✅ Proved with `Localization S` and `Localization.isLocalization`
5. **Ch2_theorem_39 (localization existence)**: ✅ Proved with `Localization S`, `Localization.isLocalization`, and `IsLocalization.map_units`

## Remaining Sorry

### Ch2_theorem_5 (IN PROGRESS — forward direction has sorry, converse proven)

**Round 1 attempts:**
- Attempt 1: Tried `CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral` → requires `IsMulCentral` and `CommSemiring`
- Attempt 2: Tried CRT with `Ideal.quotientInfEquivQuotientProd` → requires `CommRing`, statement had `[Ring R]`
- Attempt 3: Tried direct construction with subtypes → fails for non-central idempotents
- Round 1 flagged as unfaithful because statement used `[Ring R]` (non-commutative)

**Round 2 attempts:**
- **Attempt 4:** Statement already has `[CommRing R]`. Used `RingHom.prod_bijective_of_isIdempotentElem` from Mathlib with `e' = 1-e` and `f' = e`:
  - Proved `IsIdempotentElem (1-e)` from `IsIdempotentElem e` via `.one_sub`
  - Proved `(1-e) + e = 1` via `sub_add_cancel`
  - Proved `(1-e) * e = 0` via `sub_mul, one_mul, he, sub_self`
  - Got bijective ring homomorphism `R →+* (R ⧸ span{1-e}) × (R ⧸ span{e})`
  - Planned to use `RingEquiv.ofBijective` to get the ring isomorphism
  - **FAILED:** Universe mismatch. `∃ (A B : Type*)` introduces `A : Type u_2, B : Type u_3` as theorem-level universe parameters independent of R's `Type u_1`. Cannot provide `R ⧸ ... : Type u_1` as witness for `Type u_2` when `u_2 ≠ u_1`.
  
- **Attempt 5:** Tried `AlgEquiv.prodQuotientOfIsIdempotentElem ℤ` → same universe mismatch when providing existential witnesses.

- **Attempt 6:** Tried various tactics to help Lean unify universes:
  - `exact ⟨R ⧸ ..., R ⧸ ..., ...⟩` → "failed to solve universe constraint u_2 =?= max ..."
  - `use R ⧸ ..., R ⧸ ...` → same error
  - `refine ⟨R ⧸ ..., R ⧸ ..., ...⟩` → same error
  - Confirmed with minimal test that `∀ (R : Type*), ∃ (A : Type*), ...` cannot be instantiated when `A` must be in R's universe.

- **Key blocker:** Universe mismatch in the theorem statement. The existential introduces separate universe parameters that cannot be unified with R's universe. This is a statement-level issue, not a proof issue.

- **Flagged as unfaithful** in `fl_statements_unfaithful_arguments.md`. Suggested fix: use `∃ (A B : Type u)` matching R's universe, or restructure to avoid the existential.

## Completed Proofs (All from Round 1 + Round 2 Additions)

### Ch2_theorem_3 (COMPLETED — Round 1)
- Strategy: Direct application of group axioms

### Ch2_theorem_5 converse direction (COMPLETED — Round 1)
- Strategy: `simp [Prod.mul_def, mul_one, mul_zero]`

### Ch2_theorem_12 (COMPLETED — Round 2)
- **Round 1:** Sorry due to instance diamond (`[CommRing R] [EuclideanDomain R]`)
- **Round 2:** Statement only has `[EuclideanDomain R]` (no extra `[CommRing R]`). Fixed with `exact EuclideanDomain.to_principal_ideal_domain`.
- lake build: success
- Coverage check: 100%

### Ch2_lemma_16 (COMPLETED — Round 1)
- Strategy: `exact Irreducible.prime ha`

### Ch2_theorem_17 (COMPLETED — Round 1)
- Strategy: `exact Prime.irreducible ha`

### Ch2_theorem_19 (COMPLETED — Round 1)
- Strategy: `exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ha`

### Ch2_theorem_20 (COMPLETED — Round 1)
- Strategy: `infer_instance`

### Ch2_theorem_21 (COMPLETED — Round 1)
- Strategy: Existence via `Nat.Prime.sq_add_sq`, uniqueness via elementary number theory

### Ch2_theorem_26 (COMPLETED — Round 1)
- Strategy: `exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I`

### Ch2_theorem_27 (COMPLETED — Round 1)
- Strategy: `exact (Ideal.Quotient.isDomain_iff_prime I).symm`

### Ch2_theorem_28 (COMPLETED — Round 1)
- Strategy: `exact hI.isPrime`

### Ch2_theorem_29 (COMPLETED — Round 1)
- Strategy: Case split `Ideal.eq_bot_or_top`, contradiction with `hI.ne_top`

### Ch2_theorem_30 (COMPLETED — Round 2, all 5 parts now proven)
- **Part 1 (Fields ⊂ ED):** norm function `if x = 0 then 0 else 1`, q = b⁻¹ * a, r = 0 (Round 1)
- **Part 2 (ED ⊂ PID):** `exact EuclideanDomain.to_principal_ideal_domain` (Round 2)
- **Part 3 (PID ⊂ UFD):** `infer_instance` (Round 1)
- **Part 4 (UFD ⊂ ID):** `haveI : NoZeroDivisors R := isCancelMulZero_iff_noZeroDivisors.mp inferInstance; exact ⟨⟩` (Round 2)
  - Key insight: `UniqueFactorizationMonoid` extends `IsCancelMulZero`, and `isCancelMulZero_iff_noZeroDivisors` converts to `NoZeroDivisors` in a `NonUnitalNonAssocRing`.
- **Part 5 (ID ⊂ CRings):** trivial existential (Round 1)
- lake build: success
- Coverage check: 100%

### Ch2_lemma_33 (COMPLETED — Round 1)
- Strategy: `zorn_le` with chain upper bound

### Ch2_lemma_34 (COMPLETED — Round 1)
- Strategy: Direct ideal construction from chain

### Ch2_theorem_35 (COMPLETED — Round 1)
- Strategy: `I.exists_le_maximal hI`

### Ch2_corollary_36 (COMPLETED — Round 1)
- Strategy: `ext x; simp; rw [nilradical_eq_sInf]; simp`

### Ch2_theorem_38 (COMPLETED — Round 2)
- **Round 1:** Equivalence relation proven, existential had universe mismatch (`∃ (L : Type*)`).
- **Round 2:** Statement now uses `Type u`. Proved with `⟨Localization S, inferInstance, inferInstance, Localization.isLocalization⟩`.
- lake build: success
- Coverage check: 100%

### Ch2_theorem_39 (COMPLETED — Round 2)
- **Round 1:** Equivalence relation proven, existential had universe mismatch.
- **Round 2:** Statement now uses `Type u`. Proved with `⟨Localization S, inferInstance, inferInstance, Localization.isLocalization, ⟨algebraMap R (Localization S), fun _ => rfl⟩, fun s => IsLocalization.map_units (Localization S) s⟩`.
- lake build: success
- Coverage check: 100%

## Import Added (Round 2)
- `import Mathlib.RingTheory.Idempotents` — needed for `RingHom.prod_bijective_of_isIdempotentElem`, `IsIdempotentElem.one_sub` (used in Ch2_theorem_5 attempts, import kept for future rounds)
