# Proof Status Log — Chapter 2 (Round 1)

## Summary
- **Total declarations**: 39 (20 definitions + 19 theorems/lemmas)
- **Definitions**: 20/20 (all definitions match specs, no proof needed)
- **Theorems proved**: 14/19 (no sorry)
- **Theorems with sorry**: 5/19 (all flagged as unfaithful or beyond Mathlib scope)
- **Build status**: Compiles successfully (0 errors, 5 sorry warnings)
- **Coverage**: 100% — all 39 declarations from specs present in ch2.lean

## Proved Theorems (14/19)

| Theorem | Description | Proof method |
|---------|-------------|--------------|
| Ch2_theorem_3 | Units form a group; commutative ⇒ abelian | Direct term-mode: `mul_one`, `mul_inv_cancel`, `mul_assoc`, `mul_comm` |
| Ch2_theorem_5 (converse) | (1,0) in A×B is idempotent | `simp [Prod.mul_def, mul_one, mul_zero]` |
| Ch2_lemma_16 | PID: irreducible ⇒ prime | `exact Irreducible.prime ha` |
| Ch2_theorem_17 | Domain: prime ⇒ irreducible | `exact Prime.irreducible ha` |
| Ch2_theorem_19 | UFD: irreducible ⇒ prime | `exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ha` |
| Ch2_theorem_20 | PID ⇒ UFD | `infer_instance` |
| Ch2_theorem_21 | Fermat two-square (existence + uniqueness) | Existence via `Nat.Prime.sq_add_sq`; uniqueness via Lagrange identity, prime divisibility, `interval_cases` |
| Ch2_theorem_26 | Maximal ↔ R/I is field | `exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I` |
| Ch2_theorem_27 | Prime ↔ R/I is domain | `exact (Ideal.Quotient.isDomain_iff_prime I).symm` |
| Ch2_theorem_28 | Maximal ⇒ prime | `exact hI.isPrime` |
| Ch2_theorem_29 | Field: only maximal ideal is ⊥ | `rcases Ideal.eq_bot_or_top I` |
| Ch2_theorem_30 (parts 1,3,5) | Fields⊂ED, PID⊂UFD, ID⊂CRings | ED norm: `if x=0 then 0 else 1`; PID→UFD: `infer_instance`; ID→CRing: trivial |
| Ch2_theorem_35 | Proper ideal ⊂ maximal ideal | `exact I.exists_le_maximal hI` |
| Ch2_corollary_36 | ⋂ primes = nilradical | `simp only [Ideal.mem_iInf]; rw [nilradical_eq_sInf]; simp` |
| Ch2_lemma_33 | Zorn's lemma | `zorn_le` + `le_antisymm` |
| Ch2_lemma_34 | Union of chain of ideals is ideal | Manual `Submodule` construction |
| Ch2_theorem_38 (equiv. rel.) | Localization equiv. relation | Reflexivity trivial; symmetry by `h.symm`; transitivity via `linear_combination` + domain cancellation |
| Ch2_theorem_39 (equiv. rel.) | s₃-relation is equivalence | Reflexivity: `⟨1, sub_self⟩`; symmetry: `linear_combination -hs₃`; transitivity: `linear_combination` with witness `t₁*t₂*s₂` |

## Theorems with sorry (5/19) — all flagged as unfaithful

| Theorem | Description | Blocker | Unfaithful? |
|---------|-------------|---------|-------------|
| Ch2_theorem_5 (forward) | Idempotent ⇒ R ≃ A×B | Uses `[Ring R]` (non-commutative); decomposition requires e to be central | Yes |
| Ch2_theorem_12 | ED ⇒ PID | Instance diamond: `[CommRing R] [EuclideanDomain R]` | Yes |
| Ch2_theorem_30 (part 2) | ED ⊂ PID | Same instance diamond as theorem_12 | Yes |
| Ch2_theorem_30 (part 4) | UFD ⊂ ID | Trivial ring is UFD but not domain (missing `[Nontrivial R]`) | Yes |
| Ch2_theorem_38 (exist.) | Localization exists in some type | Universe mismatch: `R : Type u_1`, `∃ L : Type u_2` | Yes |
| Ch2_theorem_39 (exist.) | Localization with properties | Same universe mismatch as theorem_38 | Yes |

Note: theorem_30 has 2 internal sorry's (parts 2 and 4) but counts as 1 declaration.

## Attempt Log

### Successful on first/early attempt:
- Ch2_theorem_3, Ch2_lemma_16, Ch2_theorem_17, Ch2_theorem_19, Ch2_theorem_20,
  Ch2_theorem_26, Ch2_theorem_27, Ch2_theorem_28, Ch2_theorem_29, Ch2_theorem_35

### Required multiple attempts:
- **Ch2_theorem_30 part 1** (Fields ⊂ ED): Required `classical`, `dsimp only`, `rw [if_pos rfl, if_neg hb]`,
  and `rw [add_zero, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]` for field division.
- **Ch2_lemma_33** (Zorn): Required `.symm` on `le_antisymm` due to argument order.
- **Ch2_lemma_34** (Chain union): Required figuring out Submodule constructor fields (no `neg_mem'`).
- **Ch2_theorem_38** transitivity: Required `linear_combination` approach after `nlinarith` failed.
- **Ch2_theorem_39** transitivity: Required witness `t₁ * t₂ * s₂` and `push_cast` before `linear_combination`.
- **Ch2_corollary_36** (Nilradical): Required `simp only [Ideal.mem_iInf]` + `rw [nilradical_eq_sInf]` + `simp`.
- **Ch2_theorem_21** (Fermat): Elaborate proof using Lagrange identity, prime divisibility, and Cauchy-Schwarz bounds.

### Flagged as unfaithful (not attempted further):
- Ch2_theorem_5 forward, Ch2_theorem_12, Ch2_theorem_30 parts 2&4,
  Ch2_theorem_38 existential, Ch2_theorem_39 existential
  → See `fl_statements_unfaithful_arguments.md` for details.
