import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Order.Zorn
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Nilpotent.Defs

universe u

noncomputable section

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.1, Ring]
A ring is a set $R$ along with two binary operations, $+$ and $\times$, such that:
1. $R$ is an abelian group under $+$
2. $\times$ is associative
3. $a(b + c) = ab + ac$, $(a + b)c = ac + bc$
We also have two optional axioms:
1. $\times$ has an identity
2. $ab = ba$ (commutative rings).
\end{definition}

Natural language statement
A ring is a set R along with two binary operations + and ×, such that:
1. R is an abelian group under +
2. × is associative
3. a(b + c) = ab + ac, (a + b)c = ac + bc
Optional axioms include × having an identity, and commutativity ab = ba.
In Lean/Mathlib, NonUnitalRing captures the base axioms (abelian group under +, associative ×, distributivity) without requiring a multiplicative identity, faithfully matching the textbook's base definition where identity is optional.

Lean formalization of the natural language statement-/
def Ch2_def_1 (R : Type*) : Prop :=
  ∃ (_ : NonUnitalRing R), True

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.2, Unit]
Let $R$ be a ring. An element $a \in R$ is a unit iff it has a multiplicative inverse in $R$. We denote the collection of all invertible elements of $R$ as $R^\times$.
\end{definition}

Natural language statement
Let R be a ring. An element a ∈ R is a unit iff it has a multiplicative inverse in R. The collection of all invertible elements of R is denoted R×.

Lean formalization of the natural language statement-/
def Ch2_def_2 (R : Type*) [Ring R] (a : R) : Prop :=
  IsUnit a

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.1]
Let $R$ be a ring. The group of units, $R^\times$, is a group. If we let $R$ be a commutative ring, $R^\times$ becomes an abelian group.
\end{theorem}

Natural language statement
Let R be a ring. The group of units R× is a group: it has an identity, every element has an inverse, and the operation is associative and closed. If R is a commutative ring, then R× is an abelian group (multiplication of units is commutative).

Lean formalization of the natural language statement-/
theorem Ch2_theorem_3 :
    -- Part 1: Rˣ is a group (identity, inverses, associativity, closure)
    (∀ (R : Type*) [inst : Ring R],
      (∀ (a : Rˣ), a * 1 = a ∧ 1 * a = a) ∧
      (∀ (a : Rˣ), a * a⁻¹ = 1 ∧ a⁻¹ * a = 1) ∧
      (∀ (a b c : Rˣ), a * b * c = a * (b * c))) ∧
    -- Part 2: If R is commutative, Rˣ is abelian
    (∀ (R : Type*) [CommRing R] (a b : Rˣ), a * b = b * a) := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.3, Group ring]
Let $G$ be a group and $R$ a commutative ring. The group ring $R[G]$ is the free abelian group with basis $G$, where $\times$ is the group operation on $G$ extended linearly.
\end{definition}

Natural language statement
Let G be a group and R a commutative ring. The group ring R[G] is the free module over R with basis G, with multiplication given by extending the group operation on G linearly. In Mathlib, this is MonoidAlgebra R G.

Lean formalization of the natural language statement-/
def Ch2_def_4 (R : Type*) [CommRing R] (G : Type*) [Group G] :=
  MonoidAlgebra R G

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.2]
More generally, for a ring $R$, suppose $e \in R$ is idempotent. Then we have:
\[ R = eR \oplus (1 - e)R \]
both of which are rings. Conversely, in $A \times B$, $(1, 0)$ is idempotent. So the presence of idempotents is equivalent to the ring splitting as a product.
\end{theorem}

Natural language statement
For a ring R, if e ∈ R is idempotent (e * e = e), then there exist rings A, B and a ring isomorphism f : R ≃+* A × B sending e to (1, 0) (corresponding to the decomposition R ≅ eR × (1-e)R). Conversely, in any product ring A × B, the element (1, 0) is idempotent. Thus the existence of idempotents is equivalent to the ring decomposing as a product.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_5 :
    -- Forward: for an idempotent e, R is isomorphic to a product via a map sending e to (1, 0)
    (∀ (R : Type*) [Ring R] (e : R), e * e = e →
      ∃ (A B : Type*) (_ : Ring A) (_ : Ring B) (f : R ≃+* A × B), f e = (1, 0)) ∧
    -- Converse: (1, 0) in A × B is idempotent
    (∀ (A B : Type*) [Ring A] [Ring B],
      ((1 : A), (0 : B)) * ((1 : A), (0 : B)) = ((1 : A), (0 : B))) := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.4, Convolution]
We can think of elements of $R[G]$ as functions from $G \to R$, where $f(g_i) = r_i$. Then the product of $R[G]$ is given by
\[ fh(g) = \sum_{g_1g_2 = g} f(g_1)h(g_2) \]
which is called the convolution of $f$ and $h$.
\end{definition}

Natural language statement
Elements of R[G] can be viewed as finitely supported functions G → R. The product (convolution) of f and h in R[G] is given by (f * h)(g) = ∑_{g₁g₂ = g} f(g₁) h(g₂). In Mathlib, this is the multiplication operation on MonoidAlgebra R G, which uses finitely supported functions (Finsupp) rather than requiring G to be finite.

Lean formalization of the natural language statement-/
def Ch2_def_6 (R : Type*) [CommRing R] (G : Type*) [Group G]
    (f h : MonoidAlgebra R G) : MonoidAlgebra R G :=
  f * h

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.5, Ideal]
An ideal $I$ of a ring $R$ is a subset of $R$ such that:
1. $I$ contains $0_R$ and is closed under addition and subtraction ($I$ is a normal subgroup of $R$ with respect to addition.)
2. If $r \in I$, and $t \in R$ then $rt, tr \in I$ (stronger than saying that $I$ is closed under $\times$.)
\end{definition}

Natural language statement
An ideal I of a ring R is a subset of R such that:
1. I contains 0 and is closed under addition and subtraction (I is an additive subgroup of R).
2. For all r ∈ I and t ∈ R, both rt and tr are in I (absorption property).

Lean formalization of the natural language statement-/
def Ch2_def_7 (R : Type*) [CommRing R] (I : Set R) : Prop :=
  (0 : R) ∈ I ∧
  (∀ a b : R, a ∈ I → b ∈ I → a + b ∈ I) ∧
  (∀ a b : R, a ∈ I → b ∈ I → a - b ∈ I) ∧
  (∀ r : R, ∀ t : R, r ∈ I → r * t ∈ I ∧ t * r ∈ I)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.6, Integral domain]
A ring $R$ is an integral domain iff $1 \neq 0$, it is commutative, and there are no zero divisors in the ring.
\end{definition}

Natural language statement
A ring R is an integral domain iff 1 ≠ 0, it is commutative, and there are no zero divisors (ab = 0 implies a = 0 or b = 0).

Lean formalization of the natural language statement-/
def Ch2_def_8 (R : Type*) [CommRing R] : Prop :=
  IsDomain R

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.7, Euclidean Domain]
A commutative ring $R$ is a Euclidean domain iff it has a function $|\cdot| : R \to \mathbb{N}$ such that given $a, b$ with $b \neq 0$, we can find $r, q$ such that $a = bq + r$ and $|r| < |b|$.
\end{definition}

Natural language statement
A commutative ring R is a Euclidean domain iff there exists a function |·| : R → ℕ such that for all a, b with b ≠ 0, there exist q, r with a = bq + r and |r| < |b|.

Lean formalization of the natural language statement-/
def Ch2_def_9 (R : Type*) [CommRing R] : Prop :=
  ∃ (norm : R → ℕ), ∀ a b : R, b ≠ 0 →
    ∃ q r : R, a = b * q + r ∧ norm r < norm b

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.8, Ideal generated by elements]
The ideal generated by elements $g_1, g_2, \ldots$ is the smallest ideal containing these elements. We write this as $(g_1, g_2, \ldots)$.
\end{definition}

Natural language statement
The ideal generated by elements g₁, g₂, ... is the smallest ideal containing these elements, written (g₁, g₂, ...). In Mathlib, this is Ideal.span.

Lean formalization of the natural language statement-/
def Ch2_def_10 (R : Type*) [CommRing R] (S : Set R) : Ideal R :=
  Ideal.span S

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.9, Principal ideal domain]
A principal ideal domain is a commutative ring where all ideals are generated by one element.
\end{definition}

Natural language statement
A principal ideal domain (PID) is a commutative ring in which every ideal is generated by a single element.

Lean formalization of the natural language statement-/
def Ch2_def_11 (R : Type*) [CommRing R] : Prop :=
  IsPrincipalIdealRing R

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.1]
All Euclidean domains are PIDs.
\end{theorem}

Natural language statement
Every Euclidean domain is a principal ideal domain.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_12 (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R] :
    IsPrincipalIdealRing R := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.10, Divides]
Let $a, b \in R$. We say $a$ divides $b$ and write $a \mid b$ iff there exists some $c \in R$ such that $ac = b$.
\end{definition}

Natural language statement
Let a, b ∈ R. We say a divides b (written a ∣ b) iff there exists c ∈ R such that a * c = b.

Lean formalization of the natural language statement-/
def Ch2_def_13 (R : Type*) [CommRing R] (a b : R) : Prop :=
  a ∣ b

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.11, Irreducible]
An element $a \in R$ is called irreducible in $R$ iff it is not 0, it is not a unit, and $a = bc$ implies either $b$ or $c$ is a unit.
\end{definition}

Natural language statement
An element a ∈ R is irreducible iff a ≠ 0, a is not a unit, and whenever a = b * c, either b or c is a unit.

Lean formalization of the natural language statement-/
def Ch2_def_14 (R : Type*) [CommRing R] (a : R) : Prop :=
  Irreducible a

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.12, Prime element]
An element $a \in R$ is called prime iff $a \mid bc$ implies that $a \mid b$ or $a \mid c$.
\end{definition}

Natural language statement
An element a ∈ R is prime iff whenever a ∣ b * c, we have a ∣ b or a ∣ c.

Lean formalization of the natural language statement-/
def Ch2_def_15 (R : Type*) [CommRing R] (a : R) : Prop :=
  ∀ b c : R, a ∣ b * c → a ∣ b ∨ a ∣ c

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 2.1]
In a principal ideal domain, irreducible elements are also prime.
\end{lemma}

Natural language statement
In a principal ideal domain, every irreducible element is prime.

Lean formalization of the natural language statement-/
lemma Ch2_lemma_16 (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (a : R) (ha : Irreducible a) : Prime a := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.3]
If $R$ is an integral domain, prime elements are irreducible.
\end{theorem}

Natural language statement
If R is an integral domain, then every prime element of R is irreducible.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_17 (R : Type*) [CommRing R] [IsDomain R]
    (a : R) (ha : Prime a) : Irreducible a := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.13, Unique factorization domain]
A commutative ring $R$ is a unique factorization domain iff every element in $R$ can be expressed uniquely as a product of irreducible elements, up to order and unit multiples.
\end{definition}

Natural language statement
A commutative ring R is a unique factorization domain (UFD) iff every element can be expressed uniquely as a product of irreducible elements, up to reordering and multiplication by units.

Lean formalization of the natural language statement-/
def Ch2_def_18 (R : Type*) [CommRing R] : Prop :=
  UniqueFactorizationMonoid R

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.4]
If $R$ is a UFD, then every irreducible element is prime.
\end{theorem}

Natural language statement
If R is a unique factorization domain, then every irreducible element of R is prime.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_19 (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a : R) (ha : Irreducible a) : Prime a := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.2]
Every principal ideal domain is a unique factorization domain.
\end{theorem}

Natural language statement
Every principal ideal domain is a unique factorization domain.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_20 (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.3, Fermat's two-square theorem]
Any prime $p \in \mathbb{Z}$ where $p > 0$ and $p \equiv 1 \pmod{4}$ can be uniquely expressed as $a^2 + b^2$ up to sign changes for $a, b$.
\end{theorem}

Natural language statement
Any prime p ∈ ℤ with p > 0 and p ≡ 1 (mod 4) can be uniquely expressed as a² + b² for some integers a, b, up to sign changes.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_21 (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧
      ∀ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2 →
        (x = a ∨ x = -a) ∧ (y = b ∨ y = -b) ∨
        (x = b ∨ x = -b) ∧ (y = a ∨ y = -a) := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.14, Integral domain]
A commutative ring $R$ is an integral domain iff for $a, b \in R$, $ab = 0 \implies a = 0$ or $b = 0$.
\end{definition}

Natural language statement
A commutative ring R is an integral domain iff for all a, b ∈ R, ab = 0 implies a = 0 or b = 0.

Lean formalization of the natural language statement-/
def Ch2_def_22 (R : Type*) [CommRing R] : Prop :=
  ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.15, Field]
A commutative ring is a field iff it has no zero divisors, and every element has a multiplicative inverse.
\end{definition}

Natural language statement
A commutative ring R is a field iff it has no zero divisors and every nonzero element has a multiplicative inverse.

Lean formalization of the natural language statement-/
def Ch2_def_23 (R : Type*) [CommRing R] : Prop :=
  (∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) ∧
  (∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.16, Maximal Ideal]
An ideal $I$ of a ring $R$ is a maximal ideal iff it is the maximal element of the proper ideals of $R$.
\end{definition}

Natural language statement
An ideal I of a ring R is a maximal ideal iff it is a maximal element among the proper ideals of R, i.e., I ≠ R and there is no proper ideal J with I ⊂ J.

Lean formalization of the natural language statement-/
def Ch2_def_24 (R : Type*) [CommRing R] (I : Ideal R) : Prop :=
  I.IsMaximal

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.17, Prime ideal]
An ideal $I$ of a ring $R$ is a prime ideal iff $ab \in I \implies a \in I$ or $b \in I$.
\end{definition}

Natural language statement
An ideal I of a ring R is a prime ideal iff for all a, b ∈ R, ab ∈ I implies a ∈ I or b ∈ I.

Lean formalization of the natural language statement-/
def Ch2_def_25 (R : Type*) [CommRing R] (I : Ideal R) : Prop :=
  ∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.4]
An ideal $I$ of a ring $R$ is maximal iff $R/I$ is a field.
\end{theorem}

Natural language statement
An ideal I of a commutative ring R is maximal if and only if R/I is a field.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_26 (R : Type*) [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.5]
An ideal $I$ of a ring $R$ is prime iff $R/I$ is an integral domain.
\end{theorem}

Natural language statement
An ideal I of a commutative ring R is prime if and only if R/I is an integral domain.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_27 (R : Type*) [CommRing R] (I : Ideal R) :
    I.IsPrime ↔ IsDomain (R ⧸ I) := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.6]
Maximal ideals are always prime ideals (but not the other way around).
\end{theorem}

Natural language statement
Every maximal ideal is a prime ideal.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_28 (R : Type*) [CommRing R] (I : Ideal R) (hI : I.IsMaximal) :
    I.IsPrime := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.7]
The maximal ideal of a field is always 0.
\end{theorem}

Natural language statement
In a field, the only maximal ideal is the zero ideal {0}.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_29 (F : Type*) [Field F] (I : Ideal F) (hI : I.IsMaximal) :
    I = ⊥ := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.5]
The following inclusions hold:
\[ \text{Crings} \supset \text{ID} \supset \text{UFD} \supset \text{PID} \supset \text{ED} \supset \text{Fields} \]
\end{theorem}

Natural language statement
The following chain of inclusions holds: Fields ⊂ Euclidean Domains ⊂ PIDs ⊂ UFDs ⊂ Integral Domains ⊂ Commutative Rings.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_30 :
    -- Fields ⊂ ED (every field has a Euclidean function)
    (∀ (R : Type*) [Field R],
      ∃ (norm : R → ℕ), ∀ a b : R, b ≠ 0 →
        ∃ q r : R, a = b * q + r ∧ norm r < norm b) ∧
    -- ED ⊂ PID
    (∀ (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R], IsPrincipalIdealRing R) ∧
    -- PID ⊂ UFD
    (∀ (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R) ∧
    -- UFD ⊂ ID
    (∀ (R : Type*) [CommRing R] [UniqueFactorizationMonoid R], IsDomain R) ∧
    -- ID ⊂ CRings (every integral domain is a commutative ring, captured as:
    -- the CommRing instance is available whenever IsDomain holds, which is
    -- trivially true since IsDomain requires CommRing in its context)
    (∀ (R : Type*) [CommRing R] [IsDomain R], ∃ _ : CommRing R, True) := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.18, Maximal element]
The maximal element of some ordered set is an element $a \in S$ such that there does not exist an element such that $b > a$.
\end{definition}

Natural language statement
A maximal element of an ordered set S is an element a ∈ S such that there is no b ∈ S with b > a.

Lean formalization of the natural language statement-/
def Ch2_def_31 {S : Type*} [Preorder S] (a : S) (A : Set S) : Prop :=
  a ∈ A ∧ ∀ b ∈ A, ¬(a < b)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.19, Partial Order]
Given a set $S$, a partial order is a binary relation $\leq : S \times S \to S$ such that for all $x, y, z \in S$, we have:
1. Reflexive: $x \leq x$
2. Transitive: $x \leq y$ and $y \leq z$ implies $x \leq z$
3. Antisymmetric: $a \leq b$ and $b \leq a$ implies $a = b$
\end{definition}

Natural language statement
Given a set S, a partial order is a binary relation ≤ on S such that for all x, y, z ∈ S:
1. Reflexive: x ≤ x
2. Transitive: x ≤ y and y ≤ z implies x ≤ z
3. Antisymmetric: x ≤ y and y ≤ x implies x = y

Lean formalization of the natural language statement-/
def Ch2_def_32 (S : Type*) (le : S → S → Prop) : Prop :=
  (∀ x : S, le x x) ∧
  (∀ x y z : S, le x y → le y z → le x z) ∧
  (∀ x y : S, le x y → le y x → x = y)

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 2.2, Zorn's Lemma]
Consider a nonempty partially ordered set $S$. If it is the case that every totally ordered subset of $S$ has an upper bound, then we have that $S$ itself has a maximal element.
\end{lemma}

Natural language statement
Let S be a nonempty partially ordered set. If every totally ordered (chain) subset of S has an upper bound in S, then S has a maximal element.

Lean formalization of the natural language statement-/
lemma Ch2_lemma_33 (S : Type*) [PartialOrder S] [Nonempty S]
    (h : ∀ (C : Set S), IsChain (· ≤ ·) C → ∃ ub, ∀ c ∈ C, c ≤ ub) :
    ∃ m : S, ∀ s : S, m ≤ s → s = m := by
  sorry

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 2.3]
The union of a totally ordered set of ideals of some ring $R$ is also an ideal.
\end{lemma}

Natural language statement
The union of a nonempty totally ordered (by inclusion) collection of ideals of a ring R is itself an ideal. That is, there exists an ideal whose elements are exactly those belonging to some ideal in the chain.

Lean formalization of the natural language statement-/
lemma Ch2_lemma_34 (R : Type*) [CommRing R]
    (C : Set (Ideal R)) (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    ∃ I : Ideal R, ∀ x : R, x ∈ I ↔ ∃ J ∈ C, x ∈ J := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.8]
If $I$ is a proper ideal of some ring $R$, then $I$ is contained in some maximal ideal, so there exists a maximal ideal, unless $R = 0$.
\end{theorem}

Natural language statement
If I is a proper ideal of a ring R, then I is contained in some maximal ideal. In particular, every nonzero ring has a maximal ideal.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_35 (R : Type*) [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M := by
  sorry

/-Exact quote of the latex code of the corollary
\begin{corollary}[Corollary 2.1]
The intersection of all prime ideals of a ring is the set of all nilpotent elements of the ring.
\end{corollary}

Natural language statement
The intersection of all prime ideals of a commutative ring R equals the set of all nilpotent elements of R (the nilradical).

Lean formalization of the natural language statement-/
theorem Ch2_corollary_36 (R : Type*) [CommRing R] :
    (⨅ (P : Ideal R) (_ : P.IsPrime), P) = nilradical R := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 2.20, Quotient ring / Localization]
Given a commutative ring $R$, and a multiplicative subset $S \subseteq R$, the ring consisting of all elements of $S$ and their multiplicative inverses is called the quotient ring (or localization) and is written $R[S^{-1}]$.
\end{definition}

Natural language statement
Given a commutative ring R and a multiplicative subset S ⊆ R, the localization R[S⁻¹] is the ring obtained by formally inverting all elements of S. In Mathlib, this is captured by IsLocalization.

Lean formalization of the natural language statement-/
def Ch2_def_37 (R : Type*) [CommRing R] (S : Submonoid R)
    (L : Type*) [CommRing L] [Algebra R L] : Prop :=
  IsLocalization S L

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.6]
Let $R$ be a commutative ring, $S \subseteq R$. Also let $1 \in S$, and $S$ is multiplicatively closed with no zero divisors. Then the relation $(r_1, s_1) \sim (r_2, s_2) \iff r_1s_2 = r_2s_1$ is an equivalence relation, and the equivalence classes under this relation form a quotient ring $R[S^{-1}]$.
\end{theorem}

Natural language statement
Let R be a commutative ring and S ⊆ R a multiplicative subset containing 1 with no zero divisors. Then the relation (r₁, s₁) ∼ (r₂, s₂) ↔ r₁s₂ = r₂s₁ is an equivalence relation, and the equivalence classes form the localization R[S⁻¹].

Lean formalization of the natural language statement-/
theorem Ch2_theorem_38 (R : Type*) [CommRing R] [IsDomain R] (S : Submonoid R)
    (hS : ∀ s : S, (s : R) ≠ 0) :
    -- The relation (r₁,s₁) ∼ (r₂,s₂) ↔ r₁s₂ = r₂s₁ is an equivalence relation
    (let r := fun (p q : R × S) => (p.1 : R) * (q.2 : R) = (q.1 : R) * (p.2 : R)
     Equivalence r) ∧
    -- and the equivalence classes form the localization R[S⁻¹]
    (∃ (L : Type*) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L) := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.7]
Let $R$ be a commutative ring, $S \subseteq R$ be a multiplicative subset and $1 \in S$. Then if we take $(r_1, s_1) \sim (r_2, s_2)$ iff there exists some $s_3 \in S$ such that $s_3(r_2s_1 - s_2r_1) = 0$, this gives us a quotient ring $R[S^{-1}]$ with the following properties:
1. There exists a homomorphism from $R$ to $R[S^{-1}]$.
2. The image of all elements of $S$ in $R[S^{-1}]$ are invertible in $R[S^{-1}]$.
3. $R[S^{-1}]$ is the universal ring with these properties.
\end{theorem}

Natural language statement
Let R be a commutative ring and S ⊆ R a multiplicative subset with 1 ∈ S. Define (r₁, s₁) ∼ (r₂, s₂) iff there exists s₃ ∈ S with s₃(r₂s₁ - s₂r₁) = 0. Then this relation is an equivalence relation, and the equivalence classes form the localization R[S⁻¹] satisfying:
1. There is a ring homomorphism R → R[S⁻¹].
2. Every element of S maps to a unit in R[S⁻¹].
3. R[S⁻¹] is universal with these properties (captured by IsLocalization).

Lean formalization of the natural language statement-/
theorem Ch2_theorem_39 (R : Type*) [CommRing R] (S : Submonoid R) :
    -- The s₃-relation is an equivalence relation
    (Equivalence (fun (p q : R × S) =>
      ∃ s₃ : S, (s₃ : R) * (q.1 * (p.2 : R) - (q.2 : R) * p.1) = 0)) ∧
    -- The equivalence classes form the localization R[S⁻¹]: there exists a
    -- localization with a homomorphism R → L, all of S invertible, and universality
    (∃ (L : Type*) (_ : CommRing L) (_ : Algebra R L),
      IsLocalization S L ∧
      -- homomorphism R → L exists (via algebraMap)
      (∃ f : R →+* L, ∀ r, f r = algebraMap R L r) ∧
      -- elements of S are invertible in L
      (∀ s : S, IsUnit (algebraMap R L (s : R)))) := by
  sorry
