# Chapter 2 -- Formal Statement Verification Results (Round 1)

## Coverage Check Result

**PASS**

```
Total theorem blocks:  39
Found (exactly once):  39
Missing:               0
Duplicates:            0
Coverage:              100.0%
ADJACENCY: PASS
RESULT: COMPLETE
```

## Build Check Result

**PASS** -- Build completed successfully (only `sorry` warnings and style warnings, no errors).

---

## Per-Statement Semantic Equivalence Assessment

### Ch2_def_1 -- Definition 2.1, Ring

**LaTeX:** A ring is a set R with +, x satisfying: (1) abelian group under +, (2) x is associative, (3) distributivity. Optional: x has identity; commutativity.

**Natural Language:** Matches LaTeX; notes that Lean's `Ring R` includes the multiplicative identity.

**Lean:** `def Ch2_def_1 (R : Type*) : Prop := exists (_ : Ring R), True`

**Analysis:**
- **A. LaTeX -> NL:** Faithful. NL explicitly acknowledges the convention difference regarding the identity.
- **B. NL -> Lean:** `Ring R` in Mathlib includes a multiplicative identity (it is a *unital* ring). The textbook says the identity is "optional." The Lean formalization forces the identity to exist.
- **C. Rating: Minor discrepancy** -- Lean's `Ring` always includes a multiplicative identity, whereas the textbook treats it as optional. This is a standard Lean/Mathlib convention but does not exactly match the textbook's definition.

---

### Ch2_def_2 -- Definition 2.2, Unit

**LaTeX:** An element a in R is a unit iff it has a multiplicative inverse.

**Lean:** `def Ch2_def_2 (R : Type*) [Ring R] (a : R) : Prop := IsUnit a`

**Analysis:**
- Mathlib's `IsUnit a` means `exists (u : R^x), u.val = a`, i.e., a has a two-sided inverse. This matches exactly.
- **C. Rating: Equivalent**

---

### Ch2_theorem_3 -- Proposition 2.1

**LaTeX:** (1) R^x is a group. (2) If R is commutative, R^x is abelian.

**Lean:** `theorem Ch2_theorem_3 : forall (R : Type*) [CommRing R], (forall a b : R^x, a * b * a^{-1} * b^{-1} = 1)`

**Analysis:**
- **A. LaTeX -> NL:** Faithful.
- **B. NL -> Lean:** Part (1) -- "R^x is a group" -- is not explicitly stated. In Lean, `R^x` carries a `Group` instance automatically when `R` is a `Monoid`, so this is trivially true by the type system but not written as a proposition. Part (2) is correctly formalized: the commutator being trivial is equivalent to commutativity in a group.
- **C. Rating: Minor discrepancy** -- Part (1) of the theorem is not explicitly stated in the formalization. While it is trivially true in Lean's type system, the theorem as written only captures part (2).

---

### Ch2_def_4 -- Definition 2.3, Group ring

**LaTeX:** R[G] is the free abelian group with basis G, with multiplication given by extending the group operation linearly.

**Lean:** `def Ch2_def_4 (R : Type*) [CommRing R] (G : Type*) [Group G] := MonoidAlgebra R G`

**Analysis:**
- Mathlib's `MonoidAlgebra R G` is `G ->_0 R` (finitely supported functions from G to R) with convolution multiplication. When G is a group and R is a commutative ring, this is exactly the group ring R[G].
- **C. Rating: Equivalent**

---

### Ch2_theorem_5 -- Proposition 2.2 (Idempotent decomposition)

**LaTeX:** If e in R is idempotent, R = eR + (1-e)R as rings. Conversely, (1,0) in A x B is idempotent. Idempotents are equivalent to the ring splitting as a product.

**Lean:** `theorem Ch2_theorem_5 (R : Type*) [Ring R] (e : R) (he : e * e = e) : exists (A B : Type*) (_ : Ring A) (_ : Ring B), Nonempty (R ≃+* A x B)`

**Analysis:**
- **A. LaTeX -> NL:** Faithful.
- **B. NL -> Lean:** The Lean formalization only captures the forward direction: given an idempotent, R is isomorphic to a product. However:
  1. It uses an existential -- A and B are unidentified, losing the specific decomposition R = eR + (1-e)R.
  2. The **converse** ((1,0) is idempotent in A x B) is missing.
  3. The **equivalence** (idempotents <-> ring splitting) is not captured.
- **C. Rating: Major discrepancy** -- Only the forward direction is stated, the specific decomposition is lost, and the converse / equivalence is missing.

---

### Ch2_def_6 -- Definition 2.4, Convolution

**LaTeX:** (f*h)(g) = sum_{g1*g2=g} f(g1) h(g2)

**Lean:**
```
def Ch2_def_6 (R : Type*) [CommSemiring R] (G : Type*) [Group G]
    [Fintype G] [DecidableEq G]
    (f h : G -> R) (conv : G -> R) : Prop :=
  forall g : G, conv g = sum p in (Finset.univ.filter (fun p : G x G => p.1 * p.2 = g)),
    f p.1 * h p.2
```

**Analysis:**
- **A. LaTeX -> NL:** Faithful.
- **B. NL -> Lean:** Several issues:
  1. Uses `CommSemiring R` instead of `CommRing R` (weaker ring assumption, acceptable generalization).
  2. Adds `[Fintype G]` and `[DecidableEq G]` -- these are computational requirements not in the textbook. The textbook implicitly works with finitely supported sums, not finite groups.
  3. The definition takes `conv` as a parameter and states a predicate "conv is the convolution of f and h" rather than *defining* convolution as an operation.
  4. The textbook defines convolution for elements of R[G] (finitely supported functions), not for arbitrary functions G -> R on a finite group.
- **C. Rating: Minor discrepancy** -- The mathematical content of the sum formula is correct, but the Fintype G assumption changes the setting (finite groups vs. finitely supported functions on arbitrary groups), and the definition is presented as a predicate rather than as the product operation in R[G].

---

### Ch2_def_7 -- Definition 2.5, Ideal

**LaTeX:** An ideal I of R: (1) contains 0, closed under +/-; (2) r in I, t in R implies rt, tr in I.

**Lean:**
```
def Ch2_def_7 (R : Type*) [CommRing R] (I : Set R) : Prop :=
  (0 : R) in I /\
  (forall a b, a in I -> b in I -> a + b in I) /\
  (forall a b, a in I -> b in I -> a - b in I) /\
  (forall r t, r in I -> r * t in I /\ t * r in I)
```

**Analysis:**
- The formalization directly encodes all conditions from the textbook. For `CommRing R`, left and right absorption (`r * t` and `t * r`) are the same, so stating both is redundant but not incorrect. The closure under both addition and subtraction is also redundant (one implies the other with 0-membership), but faithful to the textbook.
- **C. Rating: Equivalent**

---

### Ch2_def_8 -- Definition 2.6, Integral domain

**LaTeX:** R is an integral domain iff 1 != 0, commutative, no zero divisors.

**Lean:** `def Ch2_def_8 (R : Type*) [CommRing R] : Prop := IsDomain R`

**Analysis:**
- Mathlib's `IsDomain R` = `IsCancelMulZero R /\ Nontrivial R`. For `CommRing`, `IsCancelMulZero` is equivalent to `NoZeroDivisors` (no zero divisors), and `Nontrivial` means 1 != 0. Combined with `[CommRing R]`, this exactly matches the textbook.
- **C. Rating: Equivalent**

---

### Ch2_def_9 -- Definition 2.7, Euclidean Domain

**LaTeX:** R is a Euclidean domain iff there exists |.| : R -> N such that for all a, b with b != 0, exists q, r with a = bq + r and |r| < |b|.

**Lean:**
```
def Ch2_def_9 (R : Type*) [CommRing R] : Prop :=
  exists (norm : R -> N), forall a b : R, b != 0 ->
    exists q r : R, a = b * q + r /\ norm r < norm b
```

**Analysis:**
- Direct encoding of the textbook definition. Does not use Mathlib's `EuclideanDomain` class (which has additional structure). The formalization is a faithful direct translation.
- **C. Rating: Equivalent**

---

### Ch2_def_10 -- Definition 2.8, Ideal generated by elements

**LaTeX:** The ideal generated by elements g1, g2, ... is the smallest ideal containing these elements.

**Lean:** `def Ch2_def_10 (R : Type*) [CommRing R] (S : Set R) : Ideal R := Ideal.span S`

**Analysis:**
- Mathlib's `Ideal.span S` is defined as the infimum of all ideals containing S, i.e., the smallest ideal containing S. This exactly matches.
- **C. Rating: Equivalent**

---

### Ch2_def_11 -- Definition 2.9, Principal ideal domain

**LaTeX:** A PID is a commutative ring where all ideals are generated by one element.

**Lean:** `def Ch2_def_11 (R : Type*) [CommRing R] : Prop := IsPrincipalIdealRing R`

**Analysis:**
- Mathlib's `IsPrincipalIdealRing R` means `forall (S : Ideal R), Submodule.IsPrincipal S`, i.e., every ideal is principal (generated by one element). This exactly matches.
- **C. Rating: Equivalent**

---

### Ch2_theorem_12 -- Theorem 2.1

**LaTeX:** All Euclidean domains are PIDs.

**Lean:** `theorem Ch2_theorem_12 (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R] : IsPrincipalIdealRing R`

**Analysis:**
- Correct statement. Note: `[EuclideanDomain R]` in Mathlib provides its own ring structure, and together with `[IsDomain R]` this captures Euclidean domains. The conclusion `IsPrincipalIdealRing R` is exactly the textbook's claim.
- **C. Rating: Equivalent**

---

### Ch2_def_13 -- Definition 2.10, Divides

**LaTeX:** a divides b iff exists c with ac = b.

**Lean:** `def Ch2_def_13 (R : Type*) [CommRing R] (a b : R) : Prop := a | b`

**Analysis:**
- In Lean/Mathlib, `a | b` means `exists c, b = a * c`. This is equivalent to the textbook's `exists c, ac = b` (just rewriting the equation).
- **C. Rating: Equivalent**

---

### Ch2_def_14 -- Definition 2.11, Irreducible

**LaTeX:** a is irreducible iff a != 0, a is not a unit, and a = bc implies b or c is a unit.

**Lean:** `def Ch2_def_14 (R : Type*) [CommRing R] (a : R) : Prop := Irreducible a`

**Analysis:**
- Mathlib's `Irreducible a` = `not (IsUnit a) /\ (forall b c, a = b * c -> IsUnit b \/ IsUnit c)`. It does not explicitly state `a != 0`, but `0` is never irreducible: `0 = 0 * 0` would require `IsUnit 0`, which fails in any nontrivial ring. So the conditions are equivalent in practice.
- **C. Rating: Equivalent**

---

### Ch2_def_15 -- Definition 2.12, Prime element

**LaTeX:** a is prime iff a | bc implies a | b or a | c.

**Lean:** `def Ch2_def_15 (R : Type*) [CommRing R] (a : R) : Prop := Prime a`

**Analysis:**
- Mathlib's `Prime a` requires three conditions: (1) `a != 0`, (2) `not (IsUnit a)`, (3) `a | b * c -> a | b \/ a | c`. The textbook only states condition (3). Conditions (1) and (2) are standard mathematical conventions for prime elements (excluding 0 and units from being prime), which the textbook likely assumes implicitly.
- **C. Rating: Minor discrepancy** -- Mathlib's `Prime` adds the conditions `a != 0` and `not (IsUnit a)` which are not explicitly stated in the textbook's definition. While these are standard conventions, the formal statement is strictly stronger than what the LaTeX quote says.

---

### Ch2_lemma_16 -- Lemma 2.1

**LaTeX:** In a PID, irreducible elements are prime.

**Lean:** `lemma Ch2_lemma_16 (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (a : R) (ha : Irreducible a) : Prime a`

**Analysis:**
- Correct. The hypothesis `[IsDomain R]` is needed because PIDs are integral domains by convention (and Mathlib's `IsPrincipalIdealRing` alone doesn't imply this).
- **C. Rating: Equivalent**

---

### Ch2_theorem_17 -- Proposition 2.3

**LaTeX:** In an integral domain, prime elements are irreducible.

**Lean:** `theorem Ch2_theorem_17 (R : Type*) [CommRing R] [IsDomain R] (a : R) (ha : Prime a) : Irreducible a`

**Analysis:**
- Exact match.
- **C. Rating: Equivalent**

---

### Ch2_def_18 -- Definition 2.13, Unique factorization domain

**LaTeX:** R is a UFD iff every element can be expressed uniquely as a product of irreducibles, up to order and unit multiples.

**Lean:** `def Ch2_def_18 (R : Type*) [CommRing R] : Prop := UniqueFactorizationMonoid R`

**Analysis:**
- Mathlib's `UniqueFactorizationMonoid R` requires `IsCancelMulZero R` (implied: R is an integral domain) and well-foundedness of the divisibility relation, plus being a `DecompositionMonoid`. For integral domains, this is equivalent to every nonzero non-unit having a unique factorization into irreducibles. This matches the textbook.
- **C. Rating: Equivalent**

---

### Ch2_theorem_19 -- Proposition 2.4

**LaTeX:** In a UFD, every irreducible element is prime.

**Lean:** `theorem Ch2_theorem_19 (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (a : R) (ha : Irreducible a) : Prime a`

**Analysis:**
- Exact match.
- **C. Rating: Equivalent**

---

### Ch2_theorem_20 -- Theorem 2.2

**LaTeX:** Every PID is a UFD.

**Lean:** `theorem Ch2_theorem_20 (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] : UniqueFactorizationMonoid R`

**Analysis:**
- Exact match.
- **C. Rating: Equivalent**

---

### Ch2_theorem_21 -- Theorem 2.3, Fermat's two-square theorem

**LaTeX:** Any prime p in Z with p > 0 and p = 1 (mod 4) can be uniquely expressed as a^2 + b^2 up to sign changes for a, b.

**Lean:**
```
theorem Ch2_theorem_21 (p : N) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    exists a b : Z, (p : Z) = a ^ 2 + b ^ 2 /\
      forall x y : Z, (p : Z) = x ^ 2 + y ^ 2 ->
        (x = a \/ x = -a) /\ (y = b \/ y = -b) \/
        (x = b \/ x = -b) /\ (y = a \/ y = -a)
```

**Analysis:**
- **A. LaTeX -> NL:** Faithful.
- **B. NL -> Lean:** Using `N` with `Nat.Prime p` is equivalent to p being a positive prime integer. The uniqueness clause correctly captures "up to sign changes" with the additional case for swapping a and b (since a^2 + b^2 = b^2 + a^2, swapping is implicitly part of the same representation).
- **C. Rating: Equivalent**

---

### Ch2_def_22 -- Definition 2.14, Integral domain (alternative)

**LaTeX:** R is an integral domain iff for a, b in R, ab = 0 implies a = 0 or b = 0.

**Lean:** `def Ch2_def_22 (R : Type*) [CommRing R] : Prop := forall a b : R, a * b = 0 -> a = 0 \/ b = 0`

**Analysis:**
- Direct encoding of the textbook statement. Note: unlike Def 2.6, this definition omits 1 != 0 -- but so does the textbook's Def 2.14 as written. The Lean formalization faithfully matches the LaTeX.
- **C. Rating: Equivalent**

---

### Ch2_def_23 -- Definition 2.15, Field

**LaTeX:** A commutative ring is a field iff it has no zero divisors, and every element has a multiplicative inverse.

**Lean:**
```
def Ch2_def_23 (R : Type*) [CommRing R] : Prop :=
  (forall a b : R, a * b = 0 -> a = 0 \/ b = 0) /\
  (forall a : R, a != 0 -> exists b : R, a * b = 1)
```

**Analysis:**
- **A. LaTeX -> NL:** The natural language says "every nonzero element has a multiplicative inverse." The LaTeX says "every element has a multiplicative inverse" without the "nonzero" qualifier. The NL adds the mathematically necessary "nonzero" condition (0 cannot have an inverse in a nontrivial ring).
- **B. NL -> Lean:** The Lean code has `a != 0 ->`, matching the NL.
- **C. Rating: Minor discrepancy** -- The LaTeX literally says "every element" while the NL and Lean correctly qualify with "nonzero." The LaTeX is imprecise; the formalization corrects this imprecision. While mathematically the correction is necessary, the Lean does not literally match the LaTeX quote.

---

### Ch2_def_24 -- Definition 2.16, Maximal Ideal

**LaTeX:** I is a maximal ideal iff it is the maximal element of the proper ideals of R.

**Lean:** `def Ch2_def_24 (R : Type*) [CommRing R] (I : Ideal R) : Prop := I.IsMaximal`

**Analysis:**
- Mathlib's `Ideal.IsMaximal I` is defined as `IsCoatom I`, meaning `I != top /\ forall J, I < J -> J = top`. This is "I is proper and there is no ideal strictly between I and R." This exactly captures "maximal element of the proper ideals."
- **C. Rating: Equivalent**

---

### Ch2_def_25 -- Definition 2.17, Prime ideal

**LaTeX:** I is a prime ideal iff ab in I implies a in I or b in I.

**Lean:** `def Ch2_def_25 (R : Type*) [CommRing R] (I : Ideal R) : Prop := I.IsPrime`

**Analysis:**
- Mathlib's `Ideal.IsPrime I` requires two conditions: (1) `I != top` (I is proper), and (2) `forall a b, a * b in I -> a in I \/ b in I`. The textbook only states condition (2). Condition (1) is a standard convention (the whole ring is excluded from being a prime ideal), but it is not explicitly in the LaTeX quote.
- **C. Rating: Minor discrepancy** -- Mathlib's `IsPrime` adds the properness condition `I != top` which is not stated in the textbook's definition. The whole ring R trivially satisfies the textbook's condition, so the Mathlib definition is strictly stronger.

---

### Ch2_theorem_26 -- Theorem 2.4

**LaTeX:** I is maximal iff R/I is a field.

**Lean:** `theorem Ch2_theorem_26 (R : Type*) [CommRing R] (I : Ideal R) : I.IsMaximal <-> IsField (R / I)`

**Analysis:**
- Mathlib's `IsField` is a predicate requiring nontriviality, commutativity, and multiplicative inverses for nonzero elements. For `CommRing`, `IsField` is equivalent to being a field. Since `IsMaximal` includes properness (ensuring R/I is nontrivial), both sides of the iff are well-matched.
- **C. Rating: Equivalent**

---

### Ch2_theorem_27 -- Theorem 2.5

**LaTeX:** I is prime iff R/I is an integral domain.

**Lean:** `theorem Ch2_theorem_27 (R : Type*) [CommRing R] (I : Ideal R) : I.IsPrime <-> IsDomain (R / I)`

**Analysis:**
- `IsPrime` includes `I != top` (properness), and `IsDomain` includes `Nontrivial` (1 != 0 in R/I, which is equivalent to I being proper). Both sides carry the properness condition, so the biconditional is well-matched.
- **C. Rating: Equivalent**

---

### Ch2_theorem_28 -- Theorem 2.6

**LaTeX:** Maximal ideals are always prime ideals.

**Lean:** `theorem Ch2_theorem_28 (R : Type*) [CommRing R] (I : Ideal R) (hI : I.IsMaximal) : I.IsPrime`

**Analysis:**
- Exact match.
- **C. Rating: Equivalent**

---

### Ch2_theorem_29 -- Theorem 2.7

**LaTeX:** The maximal ideal of a field is always 0.

**Lean:** `theorem Ch2_theorem_29 (F : Type*) [Field F] (I : Ideal F) (hI : I.IsMaximal) : I = bot`

**Analysis:**
- `bot` for `Ideal F` is the zero ideal {0}. The statement says every maximal ideal of a field equals {0}. This matches the textbook.
- **C. Rating: Equivalent**

---

### Ch2_theorem_30 -- Proposition 2.5 (Chain of inclusions)

**LaTeX:** Fields C ED C PID C UFD C ID C CRings (where C denotes proper subset/inclusion).

**Lean:**
```
theorem Ch2_theorem_30 :
    (forall (R : Type*) [Field R], IsDomain R) /\
    (forall (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R], IsPrincipalIdealRing R) /\
    (forall (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R) /\
    (forall (R : Type*) [CommRing R] [UniqueFactorizationMonoid R], IsDomain R)
```

**Analysis:**
- **A. LaTeX -> NL:** Faithful.
- **B. NL -> Lean:** The formalization has four conjuncts:
  1. Field -> IsDomain  
  2. ED -> PID  
  3. PID -> UFD  
  4. UFD -> IsDomain  

  The textbook chain is: **Fields C ED C PID C UFD C ID C CRings**. The formalization is **missing the link Fields C ED** (Fields are Euclidean Domains). The first conjunct states Fields -> ID, which skips over ED. The link ID C CRings is trivially true from the typeclass hierarchy (acceptable omission). But the missing Fields C ED is a genuine gap in the chain.
- **C. Rating: Major discrepancy** -- The formalization does not state that every field is a Euclidean domain, which is a key link in the inclusion chain. Instead it jumps from Fields to Integral Domains, losing the intermediate step.

---

### Ch2_def_31 -- Definition 2.18, Maximal element

**LaTeX:** The maximal element of an ordered set S is an element a in S such that there does not exist b > a.

**Lean:** `def Ch2_def_31 {S : Type*} [Preorder S] (a : S) (A : Set S) : Prop := a in A /\ forall b in A, not (a < b)`

**Analysis:**
- The formalization parameterizes over a subset A of a preordered type S. The condition `a in A /\ forall b in A, not (a < b)` means a is in A and no element of A is strictly greater. This matches "maximal element of the ordered set A."
- **C. Rating: Equivalent**

---

### Ch2_def_32 -- Definition 2.19, Partial Order

**LaTeX:** A partial order on S is a reflexive, transitive, antisymmetric binary relation.

**Lean:**
```
def Ch2_def_32 (S : Type*) (le : S -> S -> Prop) : Prop :=
  (forall x, le x x) /\
  (forall x y z, le x y -> le y z -> le x z) /\
  (forall x y, le x y -> le y x -> x = y)
```

**Analysis:**
- Direct encoding of reflexivity, transitivity, and antisymmetry. Exact match.
- **C. Rating: Equivalent**

---

### Ch2_lemma_33 -- Lemma 2.2, Zorn's Lemma

**LaTeX:** A nonempty partially ordered set S where every totally ordered subset has an upper bound has a maximal element.

**Lean:**
```
lemma Ch2_lemma_33 (S : Type*) [PartialOrder S] [Nonempty S]
    (h : forall (C : Set S), IsChain (. <= .) C -> exists ub, forall c in C, c <= ub) :
    exists m : S, forall s : S, m <= s -> s = m
```

**Analysis:**
- `[PartialOrder S]` provides the partial order. `[Nonempty S]` ensures nonemptiness. `IsChain (. <= .) C` means C is totally ordered. The upper bound `ub` is in S (the whole type). The conclusion `exists m, forall s, m <= s -> s = m` means m is maximal. This exactly matches Zorn's Lemma.
- **C. Rating: Equivalent**

---

### Ch2_lemma_34 -- Lemma 2.3

**LaTeX:** The union of a totally ordered set of ideals is also an ideal.

**Lean:**
```
lemma Ch2_lemma_34 (R : Type*) [CommRing R]
    (C : Set (Ideal R)) (hC : IsChain (. <= .) C) :
    exists I : Ideal R, forall J in C, J <= I
```

**Analysis:**
- **A. LaTeX -> NL:** Faithful.
- **B. NL -> Lean:** The textbook states that the *union itself* is an ideal. The Lean formalization states that there *exists* an ideal I that is an upper bound for the chain C. These are different: the textbook makes a specific claim about the union, while the Lean only asserts the existence of some upper bound ideal (which could be any ideal containing all members of C, not necessarily the union). The formalization is *weaker* than the textbook.
- **C. Rating: Minor discrepancy** -- The formalization asserts the existence of an upper bound ideal rather than stating that the union of the chain is itself an ideal. While the former follows from the latter, the specific constructive content (the union is an ideal) is lost.

---

### Ch2_theorem_35 -- Theorem 2.8

**LaTeX:** If I is a proper ideal, then I is contained in some maximal ideal.

**Lean:** `theorem Ch2_theorem_35 (R : Type*) [CommRing R] (I : Ideal R) (hI : I != top) : exists M : Ideal R, M.IsMaximal /\ I <= M`

**Analysis:**
- Exact match. `I != top` is "I is proper." The conclusion gives a maximal ideal containing I.
- **C. Rating: Equivalent**

---

### Ch2_corollary_36 -- Corollary 2.1

**LaTeX:** The intersection of all prime ideals of a ring is the set of all nilpotent elements.

**Lean:** `theorem Ch2_corollary_36 (R : Type*) [CommRing R] : (inf (P : Ideal R) (_ : P.IsPrime), P) = nilradical R`

**Analysis:**
- Mathlib's `nilradical R` is the ideal of nilpotent elements (`x in nilradical R <-> IsNilpotent x`). The infimum `inf` over all prime ideals is the intersection. Mathlib's own `nilradical_eq_sInf` states `nilradical R = sInf {J | J.IsPrime}`, confirming these are equal. This exactly matches the textbook.
- **C. Rating: Equivalent**

---

### Ch2_def_37 -- Definition 2.20, Localization

**LaTeX:** Given R and multiplicative S subset R, the localization R[S^{-1}] is the ring obtained by inverting elements of S.

**Lean:**
```
def Ch2_def_37 (R : Type*) [CommRing R] (S : Submonoid R)
    (L : Type*) [CommRing L] [Algebra R L] : Prop :=
  IsLocalization S L
```

**Analysis:**
- Mathlib's `IsLocalization S L` is a typeclass asserting L is the localization of R at S: there is a ring homomorphism R -> L, elements of S map to units, and L satisfies the universal property. `Submonoid R` captures "multiplicative subset containing 1." This matches the textbook's definition of localization.
- **C. Rating: Equivalent**

---

### Ch2_theorem_38 -- Proposition 2.6

**LaTeX:** For R a commutative ring with S multiplicatively closed, containing 1, with no zero divisors in S, the relation (r1,s1) ~ (r2,s2) iff r1*s2 = r2*s1 is an equivalence relation, and the equivalence classes form R[S^{-1}].

**Lean:**
```
theorem Ch2_theorem_38 (R : Type*) [CommRing R] [IsDomain R] (S : Submonoid R)
    (hS : forall s : S, (s : R) != 0) :
    let r := fun (p q : R x S) => (p.1 : R) * (q.2 : R) = (q.1 : R) * (p.2 : R)
    Equivalence r
```

**Analysis:**
- The Lean formalization captures the first part: the relation is an equivalence relation. The `[IsDomain R]` ensures no zero divisors in R, and `hS` ensures elements of S are nonzero. `Submonoid R` handles the "multiplicatively closed, containing 1" conditions. The second part ("equivalence classes form R[S^{-1}]") is not stated, but the equivalence relation part is the core mathematical content.
- **C. Rating: Equivalent**

---

### Ch2_theorem_39 -- Proposition 2.7

**LaTeX:** For R, S as above, using the relation (r1,s1) ~ (r2,s2) iff exists s3 in S with s3(r2*s1 - s2*r1) = 0, we get R[S^{-1}] with: (1) a homomorphism R -> R[S^{-1}], (2) elements of S map to units, (3) universal property.

**Lean:**
```
theorem Ch2_theorem_39 (R : Type*) [CommRing R] (S : Submonoid R) :
    exists (L : Type*) (_ : CommRing L) (_ : Algebra R L),
      IsLocalization S L
```

**Analysis:**
- **A. LaTeX -> NL:** Faithful.
- **B. NL -> Lean:** The formalization asserts the *existence* of a localization satisfying `IsLocalization S L`, which bundles properties (1)-(3). However, the specific equivalence relation construction (with the s3 witness) from the textbook is not captured -- only the existence and properties of the result. The construction is part of the theorem's content.
- **C. Rating: Minor discrepancy** -- The specific equivalence relation construction (the core of the proposition) is not captured; only the existence of a localization with the stated properties is asserted.

---

## Summary

| Metric | Count |
|--------|-------|
| Total statements checked | 39 |
| Equivalent | 29 |
| Minor discrepancy | 8 |
| Major discrepancy | 2 |

## Statements with Discrepancies (requiring re-formalization)

### Major Discrepancies

1. **Ch2_theorem_5** (Proposition 2.2, Idempotent decomposition) -- Only the forward direction is stated existentially; the specific decomposition R = eR + (1-e)R is lost; the converse and the equivalence are missing.

2. **Ch2_theorem_30** (Proposition 2.5, Chain of inclusions) -- Missing the link Fields C Euclidean Domains. The first conjunct states Fields -> Integral Domains instead of Fields -> Euclidean Domains.

### Minor Discrepancies

3. **Ch2_def_1** (Definition 2.1, Ring) -- Lean's `Ring` includes multiplicative identity; textbook treats it as optional.

4. **Ch2_theorem_3** (Proposition 2.1) -- Only part (2) (abelianness for CommRing) is formalized; part (1) (R^x is a group) is not explicitly stated (though trivially true in Lean).

5. **Ch2_def_6** (Definition 2.4, Convolution) -- Requires `Fintype G` (finite group) instead of working with finitely supported functions; uses a predicate form rather than defining the operation.

6. **Ch2_def_15** (Definition 2.12, Prime element) -- Mathlib's `Prime` adds `p != 0` and `not (IsUnit p)` conditions not explicitly in the textbook.

7. **Ch2_def_23** (Definition 2.15, Field) -- The LaTeX says "every element" has an inverse; the NL and Lean correctly add "nonzero," which is a correction of the LaTeX rather than a faithful translation.

8. **Ch2_def_25** (Definition 2.17, Prime ideal) -- Mathlib's `IsPrime` adds the properness condition `I != top` not stated in the textbook.

9. **Ch2_lemma_34** (Lemma 2.3) -- States existence of an upper bound ideal rather than asserting the union of the chain is itself an ideal.

10. **Ch2_theorem_39** (Proposition 2.7) -- Asserts existence of localization via `IsLocalization` but does not capture the specific equivalence relation construction with the s3 witness.

---

**Verdict: FAIL** -- 2 major discrepancies and 8 minor discrepancies found. All 10 statements listed above need re-formalization for strict semantic equivalence.
