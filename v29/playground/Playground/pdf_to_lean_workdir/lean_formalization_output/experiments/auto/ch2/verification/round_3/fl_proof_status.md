# Chapter 2 Proof Status — Round 3

## Summary

- **Total declarations**: 39 (16 theorems, 20 defs, 3 lemmas)
- **Definitions (no proof needed)**: 20 — all present
- **Theorems/lemmas needing proofs**: 19
- **Proofs completed**: 19 (ALL DONE)
- **Proofs with sorry**: 0
- **Coverage check**: 100% (39/39 statements preserved)
- **Build status**: Compiles with no errors, no sorry warnings

## Improvements from Round 2 → Round 3

Round 2 had 1 sorry instance. Round 3 resolved it:

1. **Ch2_theorem_5** (forward direction — idempotent decomposition): ✅ Proved

## Ch2_theorem_5 (COMPLETED — Round 3)

**Round 1 attempts:**
- Attempt 1: Tried CRT with `Ideal.quotientInfEquivQuotientProd` → required `CommRing`, statement originally had `[Ring R]`.
- Attempt 2: Tried direct construction with subtypes → fails for non-central idempotents.

**Round 2 attempts:**
- Attempt 3: Statement changed to `[CommRing R]`. Used `RingHom.prod_bijective_of_isIdempotentElem` with `e'=1-e, f'=e` → math proof correct but **universe mismatch**: `∃ (A B : Type*)` introduced separate universe params.
- Attempt 4: Tried `AlgEquiv.prodQuotientOfIsIdempotentElem ℤ` → same universe mismatch with `Type*`.
- Attempt 5: Various tactics to help unify universes → all failed.
- **Key blocker in Round 2**: Statement used `Type*` which created independent universe params.

**Round 3 attempts:**
- Attempt 6: Statement now uses `Type u` (fixed between rounds). Used `AlgEquiv.prodQuotientOfIsIdempotentElem ℤ` with `e' = 1-e` and `f' = e`:
  - `IsIdempotentElem (1-e)` via `he_idem.one_sub`
  - `(1-e) + e = 1` via `sub_add_cancel`
  - `(1-e) * e = 0` via `he_idem.one_sub_mul_self`
  - Got `AlgEquiv` from `R` to `(R ⧸ span{1-e}) × (R ⧸ span{e})`
  - Converted to `RingEquiv` via `.toRingEquiv`
  - For `f e = (1, 0)`: used `AlgEquiv.prodQuotientOfIsIdempotentElem_apply` to reduce to showing:
    - `mk (span{1-e}) e = 1`: proved via `Ideal.Quotient.eq` showing `e - 1 = -(1-e) ∈ span{1-e}` using `Ideal.neg_mem_iff` and `Ideal.subset_span`
    - `mk (span{e}) e = 0`: proved via `Ideal.Quotient.mk_singleton_self`
  - **First build attempt failed**: `simp only [AlgEquiv.prodQuotientOfIsIdempotentElem_apply, ...]` made no progress (couldn't see through `let` binding)
  - **Second build attempt failed**: `rw [show e = 1 - (1 - e) from by ring, map_sub, ...]` — rewrite under `mk` didn't match
  - **Third build attempt failed**: Using `ext` after `rw [_apply]` and then `simp only [Prod.fst]` — rewrite pattern not found
  - **Fourth build attempt failed**: `Ideal.neg_mem` — unknown constant (correct name is `Ideal.neg_mem_iff`)
  - **Fifth build attempt succeeded**: Proved `hmk1` and `hmk2` as separate `have` lemmas, then composed with `Prod.ext hmk1 hmk2`

- lake build: success (no errors/warnings for ch2 besides style)
- Coverage check: 39/39 statements preserved (score: 100%)
- Helper lemmas added: none
- Final proof strategy: `AlgEquiv.prodQuotientOfIsIdempotentElem ℤ` + `Ideal.Quotient.eq` + `Ideal.neg_mem_iff` + `Ideal.Quotient.mk_singleton_self`

## All Previously Completed Proofs (from Rounds 1-2, still passing)

### Ch2_theorem_3 (COMPLETED — Round 1)
- Strategy: Direct application of group axioms

### Ch2_theorem_5 converse direction (COMPLETED — Round 1)
- Strategy: `simp [Prod.mul_def, mul_one, mul_zero]`

### Ch2_theorem_12 (COMPLETED — Round 2)
- Strategy: `exact EuclideanDomain.to_principal_ideal_domain`

### Ch2_lemma_16 (COMPLETED — Round 1)
- Strategy: `exact Irreducible.prime ha`

### Ch2_theorem_17 (COMPLETED — Round 1)
- Strategy: `exact Prime.irreducible ha`

### Ch2_theorem_19 (COMPLETED — Round 1)
- Strategy: `exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ha`

### Ch2_theorem_20 (COMPLETED — Round 1)
- Strategy: `infer_instance`

### Ch2_theorem_21 (COMPLETED — Round 1)
- Strategy: `Nat.Prime.sq_add_sq` + elementary number theory for uniqueness

### Ch2_theorem_26 (COMPLETED — Round 1)
- Strategy: `exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I`

### Ch2_theorem_27 (COMPLETED — Round 1)
- Strategy: `exact (Ideal.Quotient.isDomain_iff_prime I).symm`

### Ch2_theorem_28 (COMPLETED — Round 1)
- Strategy: `exact hI.isPrime`

### Ch2_theorem_29 (COMPLETED — Round 1)
- Strategy: Case split with `Ideal.eq_bot_or_top`, contradiction

### Ch2_theorem_30 (COMPLETED — Round 2, all 5 parts)
- Part 1 (Fields ⊂ ED): custom norm function
- Part 2 (ED ⊂ PID): `exact EuclideanDomain.to_principal_ideal_domain`
- Part 3 (PID ⊂ UFD): `infer_instance`
- Part 4 (UFD ⊂ ID): `isCancelMulZero_iff_noZeroDivisors`
- Part 5 (ID ⊂ CRings): trivial

### Ch2_lemma_33 (COMPLETED — Round 1)
- Strategy: `zorn_le` with chain upper bound

### Ch2_lemma_34 (COMPLETED — Round 1)
- Strategy: Direct ideal construction from chain

### Ch2_theorem_35 (COMPLETED — Round 1)
- Strategy: `I.exists_le_maximal hI`

### Ch2_corollary_36 (COMPLETED — Round 1)
- Strategy: `ext x; simp; rw [nilradical_eq_sInf]; simp`

### Ch2_theorem_38 (COMPLETED — Round 2)
- Strategy: `Localization S` + `Localization.isLocalization`

### Ch2_theorem_39 (COMPLETED — Round 2)
- Strategy: `Localization S` + `IsLocalization.map_units`
