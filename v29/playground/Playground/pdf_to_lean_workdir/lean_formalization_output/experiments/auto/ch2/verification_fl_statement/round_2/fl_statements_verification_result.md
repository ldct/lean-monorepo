# Chapter 2 Formalized Statements Verification Result (Round 2)

## Coverage Check Result

**PASS**

```
Total theorem blocks:  39
Found (exactly once):  39
Missing:               0
Duplicates:            0
Coverage:              100.0%
ADJACENCY: PASS - All comment blocks immediately followed by correctly named declarations
RESULT: COMPLETE - All statements found exactly once, all adjacent!
```

## Build Check Result

**PASS** — Build completed successfully with only `sorry` warnings and long-line style warnings (no errors).

---

## Per-Statement Semantic Equivalence Assessment

### Ch2_def_1 — Definition 2.1 (Ring)

**LaTeX:** A ring is a set R with +, × satisfying: (1) abelian group under +, (2) × associative, (3) distributive laws. Optional: × has identity, commutativity.

**NL:** Faithful to LaTeX. Includes a note: "In Lean/Mathlib, Ring R encodes axioms 1–3 plus the existence of a multiplicative identity (which the textbook treats as optional)."

**Lean:** `∃ (_ : Ring R), True` — asks whether R admits a `Ring` structure, which in Mathlib requires a multiplicative identity.

**Mathlib check:** `Ring R` in Mathlib includes: additive abelian group, associative multiplication, distributive laws, **and multiplicative identity (1)**. The textbook lists the identity as optional.

**Assessment:**
- LaTeX → NL: Faithful. NL acknowledges the identity discrepancy.
- NL → Lean: Faithful given the noted convention.
- Overall: **Minor discrepancy** — The textbook defines rings where the multiplicative identity is optional, but Lean's `Ring` always includes it. The NL statement acknowledges this but the Lean formalization does not capture the "optional axioms" aspect of the textbook definition.

---

### Ch2_def_2 — Definition 2.2 (Unit)

**LaTeX:** An element a ∈ R is a unit iff it has a multiplicative inverse in R.

**NL:** Faithful to LaTeX.

**Lean:** `IsUnit a`

**Mathlib check:** `IsUnit a` means `∃ u : Rˣ, ↑u = a`, which is equivalent to `∃ b, a * b = 1 ∧ b * a = 1`. This matches "has a multiplicative inverse."

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_3 — Proposition 2.1 (Units form a group)

**LaTeX:** R× is a group. If R is commutative, R× is an abelian group.

**NL:** Expands "is a group" to explicit properties (identity, inverses, associativity, closure). If R commutative, R× is abelian.

**Lean:**
```
(∀ (R : Type*) [Ring R] (a : Rˣ), a * a⁻¹ = 1 ∧ a⁻¹ * a = 1) ∧
(∀ (R : Type*) [CommRing R] (a b : Rˣ), a * b = b * a)
```

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: **Minor discrepancy.** Part 1 only asserts the inverse property (`a * a⁻¹ = 1 ∧ a⁻¹ * a = 1`). The NL/LaTeX state that R× is a group, which includes closure, associativity, and identity — not just inverses. In Mathlib, `Rˣ` already carries a `Group` instance so these properties are definitionally true, but they are not explicitly stated in the formalization. The formalization captures only a subset of the claim "R× is a group."
- Overall: **Minor discrepancy** — Part 1 only captures the inverse property, not the full group structure.

---

### Ch2_def_4 — Definition 2.3 (Group Ring)

**LaTeX:** Let G be a group and R a commutative ring. The group ring R[G] is the free abelian group with basis G, with multiplication extending the group operation linearly.

**NL:** Clarifies to "free module over R with basis G." Notes Mathlib uses `MonoidAlgebra R G`.

**Lean:** `MonoidAlgebra R G` with `[CommRing R]` and `[Group G]`.

**Mathlib check:** `MonoidAlgebra R G` is `G →₀ R` (finitely supported functions G → R) with convolution multiplication. This is exactly the group ring construction when G is a group.

**Assessment:**
- LaTeX → NL: Faithful (NL corrects "free abelian group" to "free module over R").
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_5 — Proposition 2.2 (Idempotent Decomposition)

**LaTeX:** If e ∈ R is idempotent, then R = eR ⊕ (1-e)R as rings. Conversely, (1,0) in A × B is idempotent. So idempotents ↔ ring splitting as a product.

**NL:** Faithful to LaTeX. States R decomposes as a product of two rings.

**Lean:**
```
-- Forward:
(∀ (R : Type*) [Ring R] (e : R), e * e = e →
  ∃ (A B : Type*) (_ : Ring A) (_ : Ring B), Nonempty (R ≃+* A × B)) ∧
-- Converse:
(∀ (A B : Type*) [Ring A] [Ring B],
  ((1 : A), (0 : B)) * ((1 : A), (0 : B)) = ((1 : A), (0 : B)))
```

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: **Major discrepancy** in the forward direction. The textbook says R decomposes **specifically** as eR ⊕ (1-e)R — the decomposition is determined by the idempotent e. The Lean formalization says: given any idempotent e, there exist **some** A, B with R ≃+* A × B. Critically, the conclusion `∃ A B, Nonempty (R ≃+* A × B)` does not reference e at all. Since every ring has trivial idempotents (e = 0 and e = 1), and every ring trivially decomposes as R ≅ R × {0}, this forward direction is **trivially true** for any ring and any idempotent e. The textbook's statement is a meaningful structural result; the formalization is vacuous.
- The converse direction is correct: (1,0) * (1,0) = (1,0) in A × B. ✓
- Overall: **Major discrepancy** — Forward direction is trivially true and does not capture the textbook's claim.

---

### Ch2_def_6 — Definition 2.4 (Convolution)

**LaTeX:** The product in R[G] is given by convolution: (fh)(g) = Σ_{g₁g₂=g} f(g₁)h(g₂).

**NL:** Faithful. Notes Mathlib uses Finsupp.

**Lean:** `f * h` in `MonoidAlgebra R G`.

**Mathlib check:** Multiplication in `MonoidAlgebra R G` is defined as convolution via `Finsupp.sum`, matching the LaTeX formula.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_def_7 — Definition 2.5 (Ideal)

**LaTeX:** An ideal I of a ring R satisfies: (1) contains 0, closed under + and −; (2) r ∈ I, t ∈ R ⟹ rt, tr ∈ I.

**NL:** Faithful to LaTeX.

**Lean:**
```
(0 : R) ∈ I ∧
(∀ a b, a ∈ I → b ∈ I → a + b ∈ I) ∧
(∀ a b, a ∈ I → b ∈ I → a - b ∈ I) ∧
(∀ r t, r ∈ I → r * t ∈ I ∧ t * r ∈ I)
```
with `[CommRing R]` and `I : Set R`.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. The conditions match exactly. Uses `CommRing R` where textbook says "ring R" — in a commutative ring `r * t ∈ I ∧ t * r ∈ I` is redundant, but not incorrect. Closure under addition is redundant given closure under subtraction and 0 ∈ I, but again not incorrect.
- Overall: **Equivalent**

---

### Ch2_def_8 — Definition 2.6 (Integral Domain)

**LaTeX:** R is an integral domain iff 1 ≠ 0, commutative, and no zero divisors.

**NL:** Faithful to LaTeX.

**Lean:** `IsDomain R` with `[CommRing R]`.

**Mathlib check:** `IsDomain R` requires `Nontrivial R` (i.e., `∃ x y, x ≠ y`, which for rings means 1 ≠ 0) and `IsCancelMulZero R` (equivalent to no zero divisors for commutative rings). With `[CommRing R]`, this gives: commutative, 1 ≠ 0, no zero divisors.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. `IsDomain R` with `[CommRing R]` captures all three conditions.
- Overall: **Equivalent**

---

### Ch2_def_9 — Definition 2.7 (Euclidean Domain)

**LaTeX:** R is a Euclidean domain iff there exists |·| : R → ℕ such that for a, b with b ≠ 0, we can find q, r with a = bq + r and |r| < |b|.

**NL:** Faithful to LaTeX.

**Lean:**
```
∃ (norm : R → ℕ), ∀ a b : R, b ≠ 0 →
  ∃ q r : R, a = b * q + r ∧ norm r < norm b
```

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. Direct translation of the definition.
- Overall: **Equivalent**

---

### Ch2_def_10 — Definition 2.8 (Ideal Generated by Elements)

**LaTeX:** The ideal generated by g₁, g₂, ... is the smallest ideal containing these elements.

**NL:** Faithful. Notes Mathlib uses `Ideal.span`.

**Lean:** `Ideal.span S`

**Mathlib check:** `Ideal.span S` is the smallest ideal containing S. Matches exactly.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_def_11 — Definition 2.9 (Principal Ideal Domain)

**LaTeX:** A PID is a commutative ring where all ideals are generated by one element.

**NL:** Faithful.

**Lean:** `IsPrincipalIdealRing R` with `[CommRing R]`.

**Mathlib check:** `IsPrincipalIdealRing R` means `∀ (S : Ideal R), Submodule.IsPrincipal S`, i.e., every ideal is principal (generated by a single element). Matches the textbook.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_12 — Theorem 2.1 (ED → PID)

**LaTeX:** All Euclidean domains are PIDs.

**NL:** Faithful.

**Lean:** `[CommRing R] [IsDomain R] [EuclideanDomain R] : IsPrincipalIdealRing R`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. The extra `[IsDomain R]` hypothesis is redundant (EuclideanDomain implies it) but doesn't change the theorem.
- Overall: **Equivalent**

---

### Ch2_def_13 — Definition 2.10 (Divides)

**LaTeX:** a divides b iff ∃ c, ac = b.

**NL:** Faithful.

**Lean:** `a ∣ b`

**Mathlib check:** `a ∣ b` is defined as `∃ c, b = a * c`, which is equivalent to `∃ c, a * c = b`.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_def_14 — Definition 2.11 (Irreducible)

**LaTeX:** a is irreducible iff a ≠ 0, a is not a unit, and a = bc implies b or c is a unit.

**NL:** Faithful.

**Lean:** `Irreducible a`

**Mathlib check:** `Irreducible a` means `¬IsUnit a ∧ (∀ b c, a = b * c → IsUnit b ∨ IsUnit c)`. This does not explicitly state `a ≠ 0`, but in any nontrivial ring, `Irreducible 0` is false (since `0 = 0 * 0` and `¬IsUnit 0` means we'd need `IsUnit 0`, contradiction). So `Irreducible a` implies `a ≠ 0` in practice.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. The `a ≠ 0` condition from the textbook is effectively implied by Mathlib's `Irreducible` in nontrivial rings.
- Overall: **Equivalent**

---

### Ch2_def_15 — Definition 2.12 (Prime Element)

**LaTeX:** a is prime iff a | bc implies a | b or a | c.

**NL:** Faithful.

**Lean:** `∀ b c : R, a ∣ b * c → a ∣ b ∨ a ∣ c`

**Mathlib check:** Mathlib's `Prime a` additionally requires `a ≠ 0` and `¬IsUnit a`. The textbook definition (as written) only states the divisibility condition. The Lean formalization faithfully follows the textbook's literal definition.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. The formalization captures exactly the textbook's stated definition.
- Note: The textbook's definition is non-standard (standard prime element definition also requires non-zero and non-unit), but the formalization faithfully matches the textbook.
- Overall: **Equivalent**

---

### Ch2_lemma_16 — Lemma 2.1 (In PID, irreducible ⟹ prime)

**LaTeX:** In a PID, irreducible elements are prime.

**NL:** Faithful.

**Lean:** `[IsPrincipalIdealRing R] (a : R) (ha : Irreducible a) : Prime a`

**Mathlib check:** `Prime a` here includes `a ≠ 0`, `¬IsUnit a`, and the divisibility condition. Since `Irreducible a` implies `¬IsUnit a` and (in a domain) `a ≠ 0`, the conclusion `Prime a` is the natural Mathlib way to state primality.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. Uses Mathlib's standard `Prime` (stronger than Ch2_def_15's raw definition, but appropriate for this theorem statement).
- Overall: **Equivalent**

---

### Ch2_theorem_17 — Proposition 2.3 (In ID, prime ⟹ irreducible)

**LaTeX:** If R is an integral domain, prime elements are irreducible.

**NL:** Faithful.

**Lean:** `[IsDomain R] (a : R) (ha : Prime a) : Irreducible a`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_def_18 — Definition 2.13 (UFD)

**LaTeX:** R is a UFD iff every element can be expressed uniquely as a product of irreducibles, up to order and unit multiples.

**NL:** Faithful.

**Lean:** `UniqueFactorizationMonoid R`

**Mathlib check:** `UniqueFactorizationMonoid R` requires `IsCancelMulZero R` and well-foundedness of the `DvdNotUnit` relation. For a `CommRing`, this is equivalent to the textbook definition: every nonzero non-unit factors into irreducibles, and the factorization is unique up to order and associates.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_19 — Proposition 2.4 (In UFD, irreducible ⟹ prime)

**LaTeX:** If R is a UFD, every irreducible element is prime.

**NL:** Faithful.

**Lean:** `[UniqueFactorizationMonoid R] (a : R) (ha : Irreducible a) : Prime a`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_20 — Theorem 2.2 (PID → UFD)

**LaTeX:** Every PID is a UFD.

**NL:** Faithful.

**Lean:** `[IsPrincipalIdealRing R] : UniqueFactorizationMonoid R`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_21 — Theorem 2.3 (Fermat's Two-Square Theorem)

**LaTeX:** Any prime p ∈ ℤ where p > 0 and p ≡ 1 (mod 4) can be uniquely expressed as a² + b² up to sign changes.

**NL:** Faithful.

**Lean:**
```
(p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
  ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧
    ∀ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2 →
      (x = a ∨ x = -a) ∧ (y = b ∨ y = -b) ∨
      (x = b ∨ x = -b) ∧ (y = a ∨ y = -a)
```

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. Uses `Nat.Prime` (positive primes) which aligns with "p ∈ ℤ, p > 0, p prime." The uniqueness clause correctly accounts for sign changes (±a, ±b) and swapping (a↔b).
- Overall: **Equivalent**

---

### Ch2_def_22 — Definition 2.14 (Integral Domain, restated)

**LaTeX:** R is an integral domain iff for a, b ∈ R, ab = 0 implies a = 0 or b = 0.

**NL:** Faithful.

**Lean:** `∀ a b : R, a * b = 0 → a = 0 ∨ b = 0`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. This captures the no-zero-divisors condition. Note: unlike Def 2.6, this re-statement omits the 1 ≠ 0 condition. The formalization faithfully captures the textbook's re-statement.
- Overall: **Equivalent**

---

### Ch2_def_23 — Definition 2.15 (Field)

**LaTeX:** A commutative ring is a field iff it has no zero divisors, and every element has a multiplicative inverse.

**NL:** Corrects "every element" to "every nonzero element" (since 0 cannot have an inverse in a nontrivial ring). Notes this is a standard mathematical interpretation.

**Lean:**
```
(∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) ∧
(∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1)
```

**Mathlib check:** Mathlib's `IsField R` also requires nontriviality (`∃ x y, x ≠ y`). The formalization does not include this. However, in the trivial ring (0 = 1), the condition `a ≠ 0 → ∃ b, a * b = 1` is vacuously true, and the no-zero-divisors condition also holds. So the formalization doesn't exclude the trivial ring.

**Assessment:**
- LaTeX → NL: NL corrects "every element" to "every nonzero element." This is a standard mathematical interpretation, acknowledged in the NL note.
- NL → Lean: Faithful to the NL (which includes the nonzero condition).
- Overall: **Equivalent** — The three representations are internally consistent. The missing nontriviality condition is present in all three (or rather, absent from all three), so they agree.

---

### Ch2_def_24 — Definition 2.16 (Maximal Ideal)

**LaTeX:** An ideal I is maximal iff it is the maximal element of the proper ideals of R.

**NL:** Faithful, expands to: I ≠ R and no proper ideal J with I ⊂ J.

**Lean:** `I.IsMaximal`

**Mathlib check:** `Ideal.IsMaximal I` means `IsCoatom I`, i.e., `I ≠ ⊤ ∧ ∀ J, I < J → J = ⊤`. This matches "maximal among proper ideals."

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_def_25 — Definition 2.17 (Prime Ideal)

**LaTeX:** An ideal I is prime iff ab ∈ I implies a ∈ I or b ∈ I.

**NL:** Faithful.

**Lean:** `∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I`

**Mathlib check:** Mathlib's `Ideal.IsPrime I` additionally requires `I ≠ ⊤` (properness). The textbook's definition and the Lean formalization both omit this condition. Without properness, the whole ring R (= ⊤) trivially satisfies the condition.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Note: The textbook definition is non-standard (standard prime ideal definition requires properness), but the formalization faithfully matches the textbook.
- Overall: **Equivalent**

---

### Ch2_theorem_26 — Theorem 2.4 (Maximal ↔ R/I is a field)

**LaTeX:** I is maximal iff R/I is a field.

**NL:** Faithful.

**Lean:** `I.IsMaximal ↔ IsField (R ⧸ I)`

**Mathlib check:** `IsField (R ⧸ I)` means: nontrivial, commutative, and every nonzero element has an inverse. `I.IsMaximal` means: I is a coatom (maximal proper ideal). This iff is a standard algebraic result.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_27 — Theorem 2.5 (Prime ↔ R/I is an integral domain)

**LaTeX:** I is prime iff R/I is an integral domain.

**NL:** Faithful.

**Lean:** `I.IsPrime ↔ IsDomain (R ⧸ I)`

**Mathlib check:** `I.IsPrime` requires `I ≠ ⊤` and the prime condition. `IsDomain (R ⧸ I)` requires nontriviality (equiv. to `I ≠ ⊤`) and no zero divisors (equiv. to the prime condition). This iff is standard.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. Uses Mathlib's `IsPrime` (which includes properness), matching the standard mathematical theorem.
- Overall: **Equivalent**

---

### Ch2_theorem_28 — Theorem 2.6 (Maximal ⟹ Prime)

**LaTeX:** Maximal ideals are always prime ideals.

**NL:** Faithful.

**Lean:** `(hI : I.IsMaximal) : I.IsPrime`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_29 — Theorem 2.7 (Maximal ideal of a field is 0)

**LaTeX:** The maximal ideal of a field is always 0.

**NL:** In a field, the only maximal ideal is the zero ideal {0}.

**Lean:** `[Field F] (I : Ideal F) (hI : I.IsMaximal) : I = ⊥`

**Mathlib check:** `⊥` for ideals is the zero ideal {0}.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_30 — Proposition 2.5 (Chain of Inclusions)

**LaTeX:** CRings ⊃ ID ⊃ UFD ⊃ PID ⊃ ED ⊃ Fields

**NL:** Reverses to: Fields ⊂ ED ⊂ PID ⊂ UFD ⊂ ID ⊂ CRings.

**Lean:** Four conjuncts:
1. Fields ⊂ ED (every field has a Euclidean function)
2. ED ⊂ PID
3. PID ⊂ UFD
4. UFD ⊂ ID

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: **Minor discrepancy.** The chain has 5 inclusion links (Fields⊂ED, ED⊂PID, PID⊂UFD, UFD⊂ID, ID⊂CRings). The formalization only includes 4 — the link "ID ⊂ CRings" (integral domains are commutative rings) is missing. While this is trivially true in Lean's type system (IsDomain is defined on top of a Semiring, and CommRing is already in the context), the textbook explicitly includes it in the chain.
- Overall: **Minor discrepancy** — one inclusion from the chain (ID ⊂ CRings) is omitted.

---

### Ch2_def_31 — Definition 2.18 (Maximal Element)

**LaTeX:** The maximal element of an ordered set is a ∈ S such that no b > a exists.

**NL:** Faithful.

**Lean:** `a ∈ A ∧ ∀ b ∈ A, ¬(a < b)`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. `a ∈ A` captures "a ∈ S" and `¬(a < b)` captures "no b > a."
- Overall: **Equivalent**

---

### Ch2_def_32 — Definition 2.19 (Partial Order)

**LaTeX:** A partial order ≤ on S is reflexive, transitive, and antisymmetric.

**NL:** Faithful.

**Lean:**
```
(∀ x, le x x) ∧
(∀ x y z, le x y → le y z → le x z) ∧
(∀ x y, le x y → le y x → x = y)
```

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. Each axiom directly translated.
- Overall: **Equivalent**

---

### Ch2_lemma_33 — Lemma 2.2 (Zorn's Lemma)

**LaTeX:** In a nonempty partially ordered set S, if every totally ordered subset has an upper bound, then S has a maximal element.

**NL:** Faithful.

**Lean:**
```
[PartialOrder S] [Nonempty S]
(h : ∀ (C : Set S), IsChain (· ≤ ·) C → ∃ ub, ∀ c ∈ C, c ≤ ub) :
  ∃ m : S, ∀ s : S, m ≤ s → s = m
```

**Mathlib check:** `IsChain (· ≤ ·) C` means `∀ a ∈ C, ∀ b ∈ C, a ≠ b → a ≤ b ∨ b ≤ a` — a total order on C. The upper bound `ub : S` is in S. The conclusion `∀ s, m ≤ s → s = m` means m is maximal.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_lemma_34 — Lemma 2.3 (Union of Chain of Ideals)

**LaTeX:** The union of a totally ordered set of ideals is an ideal.

**NL:** Adds "nonempty" and clarifies: the union forms an ideal whose elements are those belonging to some ideal in the chain.

**Lean:**
```
(C : Set (Ideal R)) (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
  ∃ I : Ideal R, ∀ x : R, x ∈ I ↔ ∃ J ∈ C, x ∈ J
```

**Assessment:**
- LaTeX → NL: Faithful (NL's "nonempty" is implicit in the LaTeX).
- NL → Lean: Faithful. The conclusion says there exists an ideal I whose membership is equivalent to belonging to some ideal in the chain.
- Overall: **Equivalent**

---

### Ch2_theorem_35 — Theorem 2.8 (Proper ideal contained in maximal ideal)

**LaTeX:** If I is a proper ideal, then I is contained in some maximal ideal.

**NL:** Faithful.

**Lean:** `(I : Ideal R) (hI : I ≠ ⊤) : ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M`

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful. `I ≠ ⊤` captures "proper ideal"; `M.IsMaximal ∧ I ≤ M` captures "contained in a maximal ideal."
- Overall: **Equivalent**

---

### Ch2_corollary_36 — Corollary 2.1 (Intersection of Primes = Nilradical)

**LaTeX:** The intersection of all prime ideals = set of all nilpotent elements.

**NL:** Faithful.

**Lean:** `(⨅ (P : Ideal R) (_ : P.IsPrime), P) = nilradical R`

**Mathlib check:**
- `⨅ (P : Ideal R) (_ : P.IsPrime), P` is the infimum (intersection) of all prime ideals. ✓
- `nilradical R` is the ideal of nilpotent elements (`x ∈ nilradical R ↔ IsNilpotent x`). ✓
- `nilradical_eq_sInf` confirms `nilradical R = sInf {J | J.IsPrime}`, consistent with the formalization.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_def_37 — Definition 2.20 (Localization)

**LaTeX:** Given R and multiplicative subset S, the localization R[S⁻¹] is the ring obtained by inverting all elements of S.

**NL:** Faithful. Notes Mathlib uses `IsLocalization`.

**Lean:** `IsLocalization S L` with `[Algebra R L]`.

**Mathlib check:** `IsLocalization S L` characterizes L as the localization of R at S: it has an algebra map R → L, all elements of S become units in L, and L satisfies a universal property.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: Faithful.
- Overall: **Equivalent**

---

### Ch2_theorem_38 — Proposition 2.6 (Localization Equivalence Relation)

**LaTeX:** Let R be a commutative ring, S ⊆ R with 1 ∈ S, S multiplicatively closed, no zero divisors. The relation (r₁,s₁) ∼ (r₂,s₂) iff r₁s₂ = r₂s₁ is an equivalence relation, **and the equivalence classes form a quotient ring R[S⁻¹]**.

**NL:** Faithful to LaTeX.

**Lean:**
```
[IsDomain R] (S : Submonoid R) (hS : ∀ s : S, (s : R) ≠ 0) :
  let r := fun (p q : R × S) => (p.1 : R) * (q.2 : R) = (q.1 : R) * (p.2 : R)
  Equivalence r
```

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: **Major discrepancy.** The textbook and NL state two things: (1) the relation is an equivalence relation, and (2) the equivalence classes form the localization R[S⁻¹]. The Lean formalization only proves (1) — that the relation is an equivalence. The crucial second part (the equivalence classes form a ring, specifically the localization) is completely missing.
- Overall: **Major discrepancy** — missing the conclusion that the equivalence classes form the localization.

---

### Ch2_theorem_39 — Proposition 2.7 (General Localization)

**LaTeX:** Define (r₁,s₁) ∼ (r₂,s₂) iff ∃ s₃ ∈ S with s₃(r₂s₁ − s₂r₁) = 0. This gives a quotient ring R[S⁻¹] with: (1) homomorphism R → R[S⁻¹], (2) elements of S are invertible in R[S⁻¹], (3) universal property.

**NL:** Faithful.

**Lean:**
```
(Equivalence (fun (p q : R × S) =>
  ∃ s₃ : S, (s₃ : R) * (q.1 * (p.2 : R) - (q.2 : R) * p.1) = 0)) ∧
(∃ (L : Type*) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L)
```

**Mathlib check:** `IsLocalization S L` bundles the homomorphism (via `Algebra R L`), invertibility of S, and the universal property.

**Assessment:**
- LaTeX → NL: Faithful.
- NL → Lean: **Minor discrepancy.** The Lean formalization proves two independent claims: (a) the s₃-relation is an equivalence, and (b) there exists a localization. However, the textbook's key claim is that *this specific equivalence relation gives rise to* the localization — i.e., the localization is *constructed from* the equivalence classes. The formalization does not connect these two claims; the localization L could be any localization, not necessarily the one built from the equivalence classes. The structural link between the equivalence relation and the localization is lost.
- Overall: **Minor discrepancy** — the relationship between the equivalence relation and the localization construction is not captured.

---

## Summary

| Metric | Count |
|--------|-------|
| Total statements checked | 39 |
| Equivalent | 34 |
| Minor discrepancy | 3 |
| Major discrepancy | 2 |

## Statements with Discrepancies

### Major Discrepancies (must be re-formalized)

1. **Ch2_theorem_5** (Proposition 2.2 — Idempotent Decomposition): The forward direction `e * e = e → ∃ A B, R ≃+* A × B` does not reference the idempotent e in the conclusion at all. Since every ring has trivial idempotents (0 and 1) and every ring trivially decomposes as R ≅ R × {0}, this forward direction is trivially true and vacuous. The textbook's claim is that R specifically decomposes as eR ⊕ (1-e)R — the decomposition must be tied to the given idempotent.

2. **Ch2_theorem_38** (Proposition 2.6 — Localization Equivalence Relation): The formalization only proves the relation is an equivalence relation. The textbook also states that the equivalence classes form the localization R[S⁻¹], which is the main content of the proposition. This second conclusion is entirely missing.

### Minor Discrepancies (should be re-formalized for strict equivalence)

1. **Ch2_def_1** (Definition 2.1 — Ring): Lean's `Ring R` always includes a multiplicative identity, while the textbook treats it as optional. The NL acknowledges this difference.

2. **Ch2_theorem_3** (Proposition 2.1 — Units form a group): Part 1 only asserts the inverse property of units, not the full group structure (closure, associativity, identity). While these are definitionally true for `Rˣ` in Mathlib, the formalization does not explicitly state "Rˣ is a group."

3. **Ch2_theorem_30** (Proposition 2.5 — Chain of Inclusions): The link "ID ⊂ CRings" (integral domains are commutative rings) is missing from the formalization. The textbook's chain has 5 links; the formalization only has 4.

4. **Ch2_theorem_39** (Proposition 2.7 — General Localization): The formalization proves the equivalence relation and the existence of a localization as independent claims, without connecting them. The textbook's claim is that the localization is constructed from the equivalence classes.
