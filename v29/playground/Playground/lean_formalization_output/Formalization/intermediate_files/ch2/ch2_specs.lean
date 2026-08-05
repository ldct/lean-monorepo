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
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.Idempotents

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
  exact ⟨fun R inst => ⟨fun a => ⟨mul_one a, one_mul a⟩,
    fun a => ⟨mul_inv_cancel a, inv_mul_cancel a⟩,
    fun a b c => mul_assoc a b c⟩,
    fun R _ a b => mul_comm a b⟩

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
    -- Forward: for an idempotent e in a commutative ring, R is isomorphic to a product via a map sending e to (1, 0)
    (∀ (R : Type u) [CommRing R] (e : R), e * e = e →
      ∃ (A B : Type u) (_ : Ring A) (_ : Ring B) (f : R ≃+* A × B), f e = (1, 0)) ∧
    -- Converse: (1, 0) in A × B is idempotent
    (∀ (A B : Type u) [Ring A] [Ring B],
      ((1 : A), (0 : B)) * ((1 : A), (0 : B)) = ((1 : A), (0 : B))) := by
  constructor
  · intro R _inst e he
    /- PROOF ATTEMPTS LOG (do not delete — helps next iteration):
      Attempt 1 (Round 1): Tried CRT with Ideal.quotientInfEquivQuotientProd → requires CommRing,
        statement originally had [Ring R]. Flagged as unfaithful for non-central idempotents.
      Attempt 2 (Round 2): Statement has [CommRing R]. Used
        RingHom.prod_bijective_of_isIdempotentElem with e'=1-e, f'=e to get bijective map
        R →+* (R ⧸ span{1-e}) × (R ⧸ span{e}), then RingEquiv.ofBijective.
        Math proof is complete and correct. But providing the existential witnesses fails:
        ∃ (A B : Type*) introduces A : Type u_2, B : Type u_3 as separate universe
        parameters, while witnesses R ⧸ ... are in Type u_1. Lean cannot unify u_2 = u_1.
      Key blocker: Universe mismatch. The existential ∃ (A B : Type*) creates universe
        parameters independent of R's universe. Fix: change to same universe as R.
    -/
    sorry
  · intro A B _instA _instB
    simp [Prod.mul_def, mul_one, mul_zero]

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
theorem Ch2_theorem_12 (R : Type*) [EuclideanDomain R] :
    IsPrincipalIdealRing R := by
  exact EuclideanDomain.to_principal_ideal_domain

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
  exact Irreducible.prime ha

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 2.3]
If $R$ is an integral domain, prime elements are irreducible.
\end{theorem}

Natural language statement
If R is an integral domain, then every prime element of R is irreducible.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_17 (R : Type*) [CommRing R] [IsDomain R]
    (a : R) (ha : Prime a) : Irreducible a := by
  exact Prime.irreducible ha

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
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ha

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.2]
Every principal ideal domain is a unique factorization domain.
\end{theorem}

Natural language statement
Every principal ideal domain is a unique factorization domain.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_20 (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R := by
  infer_instance

-- Increased heartbeats for the uniqueness proof (many nlinarith calls)
set_option maxHeartbeats 800000 in
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
  -- Existence from Mathlib's Fermat two-square theorem
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (by omega : p % 4 ≠ 3)
  refine ⟨(a : ℤ), (b : ℤ), ?_, ?_⟩
  · exact_mod_cast hab.symm
  -- Uniqueness via elementary number theory
  intro x y hxy
  have habz : (p : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hab.symm
  have hp_pos : (p : ℤ) > 0 := by exact_mod_cast hp.pos
  have hp_int : Prime (p : ℤ) := by rwa [← Nat.prime_iff_prime_int]
  -- Product identity: (ax-by)(ax+by) = p(x²-b²)
  have hprod : ((a : ℤ) * x - (b : ℤ) * y) * ((a : ℤ) * x + (b : ℤ) * y) =
      (p : ℤ) * (x ^ 2 - (b : ℤ) ^ 2) := by
    have lhs : ((a : ℤ) * x - (b : ℤ) * y) * ((a : ℤ) * x + (b : ℤ) * y) =
        (a : ℤ) ^ 2 * x ^ 2 - (b : ℤ) ^ 2 * y ^ 2 := by ring
    rw [lhs]
    have h1 : (a : ℤ) ^ 2 = (p : ℤ) - (b : ℤ) ^ 2 := by linarith
    have h2 : y ^ 2 = (p : ℤ) - x ^ 2 := by linarith
    rw [h1, h2]; ring
  -- p divides the product
  have hdvd_prod : (p : ℤ) ∣ ((a : ℤ) * x - (b : ℤ) * y) * ((a : ℤ) * x + (b : ℤ) * y) :=
    ⟨x ^ 2 - (b : ℤ) ^ 2, hprod⟩
  -- Lagrange identities: (ax∓by)² + (ay±bx)² = (a²+b²)(x²+y²) = p²
  have hid1 : ((a : ℤ) * x - (b : ℤ) * y) ^ 2 + ((a : ℤ) * y + (b : ℤ) * x) ^ 2 =
      (p : ℤ) ^ 2 := by
    have : ((a : ℤ) * x - (b : ℤ) * y) ^ 2 + ((a : ℤ) * y + (b : ℤ) * x) ^ 2 =
      ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) * (x ^ 2 + y ^ 2) := by ring
    rw [this, ← habz, ← hxy]; ring
  have hid2 : ((a : ℤ) * x + (b : ℤ) * y) ^ 2 + ((a : ℤ) * y - (b : ℤ) * x) ^ 2 =
      (p : ℤ) ^ 2 := by
    have : ((a : ℤ) * x + (b : ℤ) * y) ^ 2 + ((a : ℤ) * y - (b : ℤ) * x) ^ 2 =
      ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) * (x ^ 2 + y ^ 2) := by ring
    rw [this, ← habz, ← hxy]; ring
  -- Cauchy-Schwarz bounds from the identities
  have hcs1 : ((a : ℤ) * x - (b : ℤ) * y) ^ 2 ≤ (p : ℤ) ^ 2 := by
    linarith [sq_nonneg ((a : ℤ) * y + (b : ℤ) * x)]
  have hcs2 : ((a : ℤ) * x + (b : ℤ) * y) ^ 2 ≤ (p : ℤ) ^ 2 := by
    linarith [sq_nonneg ((a : ℤ) * y - (b : ℤ) * x)]
  -- Helper: if p | n and n² ≤ p² then n ∈ {0, p, -p}
  have bound : ∀ n : ℤ, (p : ℤ) ∣ n → n ^ 2 ≤ (p : ℤ) ^ 2 →
      n = 0 ∨ n = (p : ℤ) ∨ n = -(p : ℤ) := by
    intro n hdvd hle
    obtain ⟨k, hk⟩ := hdvd
    have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
    have hpk : n ^ 2 = (p : ℤ) ^ 2 * k ^ 2 := by rw [hk]; ring
    have h1 : (p : ℤ) ^ 2 * k ^ 2 ≤ (p : ℤ) ^ 2 := by linarith
    have hkb : k ^ 2 ≤ 1 := by
      by_contra h; push_neg at h; nlinarith
    have : k ≤ 1 := by nlinarith
    have : -1 ≤ k := by nlinarith
    interval_cases k <;> omega
  -- Helper: u² = v² implies u = v or u = -v
  have sq_eq : ∀ u v : ℤ, u ^ 2 = v ^ 2 → u = v ∨ u = -v := by
    intro u v h
    have : (u - v) * (u + v) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  -- Helper: from a·u = b·v and p = u²+v², deduce u² = b² and v² = a²
  have from_eq : ∀ u v : ℤ, (a : ℤ) * u = (b : ℤ) * v → (p : ℤ) = u ^ 2 + v ^ 2 →
      u ^ 2 = (b : ℤ) ^ 2 ∧ v ^ 2 = (a : ℤ) ^ 2 := by
    intro u v huv hpuv
    have h2 : ((a : ℤ) * u) ^ 2 = ((b : ℤ) * v) ^ 2 := by rw [huv]
    have h3 : (a : ℤ) ^ 2 * u ^ 2 = (b : ℤ) ^ 2 * v ^ 2 := by
      linarith [mul_pow (a : ℤ) u 2, mul_pow (b : ℤ) v 2]
    constructor <;> nlinarith
  -- Main case split: since p is prime and p | (ax-by)(ax+by),
  -- either p | (ax-by) or p | (ax+by)
  rcases hp_int.dvd_or_dvd hdvd_prod with hdvd_minus | hdvd_plus
  · -- Case: p | (ax - by)
    rcases bound _ hdvd_minus hcs1 with h | h | h
    · -- Subcase: ax - by = 0, i.e., ax = by
      have haxby : (a : ℤ) * x = (b : ℤ) * y := by linarith
      obtain ⟨hxb, hya⟩ := from_eq x y haxby hxy
      right; exact ⟨sq_eq x (b : ℤ) hxb, sq_eq y (a : ℤ) hya⟩
    · -- Subcase: ax - by = p, then ay + bx = 0 from Lagrange identity
      have haybx_zero : (a : ℤ) * y + (b : ℤ) * x = 0 := by
        nlinarith [sq_nonneg ((a : ℤ) * y + (b : ℤ) * x)]
      obtain ⟨hyb, hxa⟩ := from_eq y (-x) (by linarith) (by linarith [sq_nonneg x])
      left; exact ⟨sq_eq x (a : ℤ) (by nlinarith), sq_eq y (b : ℤ) hyb⟩
    · -- Subcase: ax - by = -p, same conclusion
      have haybx_zero : (a : ℤ) * y + (b : ℤ) * x = 0 := by
        nlinarith [sq_nonneg ((a : ℤ) * y + (b : ℤ) * x)]
      obtain ⟨hyb, hxa⟩ := from_eq y (-x) (by linarith) (by linarith [sq_nonneg x])
      left; exact ⟨sq_eq x (a : ℤ) (by nlinarith), sq_eq y (b : ℤ) hyb⟩
  · -- Case: p | (ax + by)
    rcases bound _ hdvd_plus hcs2 with h | h | h
    · -- Subcase: ax + by = 0, i.e., ax = b·(-y)
      have haxby : (a : ℤ) * x = (b : ℤ) * (-y) := by linarith
      obtain ⟨hxb, hya⟩ := from_eq x (-y) haxby (by linarith [sq_nonneg y])
      right; exact ⟨sq_eq x (b : ℤ) hxb, sq_eq y (a : ℤ) (by nlinarith)⟩
    · -- Subcase: ax + by = p, then ay - bx = 0 from Lagrange identity
      have haybx_zero : (a : ℤ) * y - (b : ℤ) * x = 0 := by
        nlinarith [sq_nonneg ((a : ℤ) * y - (b : ℤ) * x)]
      obtain ⟨hyb, hxa⟩ := from_eq y x (by linarith) (by linarith)
      left; exact ⟨sq_eq x (a : ℤ) hxa, sq_eq y (b : ℤ) hyb⟩
    · -- Subcase: ax + by = -p, same conclusion
      have haybx_zero : (a : ℤ) * y - (b : ℤ) * x = 0 := by
        nlinarith [sq_nonneg ((a : ℤ) * y - (b : ℤ) * x)]
      obtain ⟨hyb, hxa⟩ := from_eq y x (by linarith) (by linarith)
      left; exact ⟨sq_eq x (a : ℤ) hxa, sq_eq y (b : ℤ) hyb⟩

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
  exact Ideal.Quotient.maximal_ideal_iff_isField_quotient I

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.5]
An ideal $I$ of a ring $R$ is prime iff $R/I$ is an integral domain.
\end{theorem}

Natural language statement
An ideal I of a commutative ring R is prime if and only if R/I is an integral domain.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_27 (R : Type*) [CommRing R] (I : Ideal R) :
    I.IsPrime ↔ IsDomain (R ⧸ I) := by
  exact (Ideal.Quotient.isDomain_iff_prime I).symm

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.6]
Maximal ideals are always prime ideals (but not the other way around).
\end{theorem}

Natural language statement
Every maximal ideal is a prime ideal.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_28 (R : Type*) [CommRing R] (I : Ideal R) (hI : I.IsMaximal) :
    I.IsPrime := by
  exact hI.isPrime

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.7]
The maximal ideal of a field is always 0.
\end{theorem}

Natural language statement
In a field, the only maximal ideal is the zero ideal {0}.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_29 (F : Type*) [Field F] (I : Ideal F) (hI : I.IsMaximal) :
    I = ⊥ := by
  rcases Ideal.eq_bot_or_top I with h | h
  · exact h
  · exact absurd h hI.ne_top

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
    (∀ (R : Type*) [EuclideanDomain R], IsPrincipalIdealRing R) ∧
    -- PID ⊂ UFD
    (∀ (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R) ∧
    -- UFD ⊂ ID
    (∀ (R : Type*) [CommRing R] [Nontrivial R] [UniqueFactorizationMonoid R], IsDomain R) ∧
    -- ID ⊂ CRings (every integral domain is a commutative ring, captured as:
    -- the CommRing instance is available whenever IsDomain holds, which is
    -- trivially true since IsDomain requires CommRing in its context)
    (∀ (R : Type*) [CommRing R] [IsDomain R], ∃ _ : CommRing R, True) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Fields ⊂ ED: use norm(x) = 0 for x = 0, 1 for x ≠ 0; q = a/b, r = 0
    intro R _
    classical
    refine ⟨fun x => if x = 0 then 0 else 1, fun a b hb => ⟨b⁻¹ * a, 0, ?_, ?_⟩⟩
    · rw [add_zero, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
    · dsimp only; rw [if_pos rfl, if_neg hb]; exact Nat.zero_lt_one
  · -- ED ⊂ PID
    intro R _
    exact EuclideanDomain.to_principal_ideal_domain
  · intro R _ _ _; infer_instance
  · intro R _ _ _
    haveI : NoZeroDivisors R :=
      isCancelMulZero_iff_noZeroDivisors.mp inferInstance
    exact ⟨⟩
  · intro R inst _; exact ⟨inst, trivial⟩

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
  obtain ⟨m, hm⟩ := zorn_le (α := S) (fun c hc => by
    obtain ⟨ub, hub⟩ := h c hc
    exact ⟨ub, fun _ ha => hub _ ha⟩)
  exact ⟨m, fun s hs => (le_antisymm hs (hm hs)).symm⟩

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
  refine ⟨{
    carrier := {x | ∃ J ∈ C, x ∈ J}
    add_mem' := ?_
    zero_mem' := ?_
    smul_mem' := ?_
  }, fun x => Iff.rfl⟩
  · intro _ _ ha hb
    obtain ⟨J₁, hJ₁C, hxJ₁⟩ := ha
    obtain ⟨J₂, hJ₂C, hyJ₂⟩ := hb
    rcases hC.total hJ₁C hJ₂C with h | h
    · exact ⟨J₂, hJ₂C, J₂.add_mem (h hxJ₁) hyJ₂⟩
    · exact ⟨J₁, hJ₁C, J₁.add_mem hxJ₁ (h hyJ₂)⟩
  · obtain ⟨J, hJC⟩ := hne
    exact ⟨J, hJC, J.zero_mem⟩
  · intro r _ hx
    obtain ⟨J, hJC, hxJ⟩ := hx
    exact ⟨J, hJC, J.smul_mem r hxJ⟩

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 2.8]
If $I$ is a proper ideal of some ring $R$, then $I$ is contained in some maximal ideal, so there exists a maximal ideal, unless $R = 0$.
\end{theorem}

Natural language statement
If I is a proper ideal of a ring R, then I is contained in some maximal ideal. In particular, every nonzero ring has a maximal ideal.

Lean formalization of the natural language statement-/
theorem Ch2_theorem_35 (R : Type*) [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M := by
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
  exact ⟨M, hM, hIM⟩

/-Exact quote of the latex code of the corollary
\begin{corollary}[Corollary 2.1]
The intersection of all prime ideals of a ring is the set of all nilpotent elements of the ring.
\end{corollary}

Natural language statement
The intersection of all prime ideals of a commutative ring R equals the set of all nilpotent elements of R (the nilradical).

Lean formalization of the natural language statement-/
theorem Ch2_corollary_36 (R : Type*) [CommRing R] :
    (⨅ (P : Ideal R) (_ : P.IsPrime), P) = nilradical R := by
  ext x
  simp only [Ideal.mem_iInf]
  rw [nilradical_eq_sInf]
  simp only [Ideal.mem_sInf, Set.mem_setOf_eq]

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
theorem Ch2_theorem_38 (R : Type u) [CommRing R] [IsDomain R] (S : Submonoid R)
    (hS : ∀ s : S, (s : R) ≠ 0) :
    -- The relation (r₁,s₁) ∼ (r₂,s₂) ↔ r₁s₂ = r₂s₁ is an equivalence relation
    (let r := fun (p q : R × S) => (p.1 : R) * (q.2 : R) = (q.1 : R) * (p.2 : R)
     Equivalence r) ∧
    -- and the equivalence classes form the localization R[S⁻¹]
    (∃ (L : Type u) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L) := by
  constructor
  · -- Equivalence relation
    constructor
    · intro ⟨_, _⟩; rfl
    · intro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
      change r₂ * (s₁ : R) = r₁ * (s₂ : R)
      change r₁ * (s₂ : R) = r₂ * (s₁ : R) at h
      exact h.symm
    · intro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ h₁₂ h₂₃
      change r₁ * (s₃ : R) = r₃ * (s₁ : R)
      change r₁ * (s₂ : R) = r₂ * (s₁ : R) at h₁₂
      change r₂ * (s₃ : R) = r₃ * (s₂ : R) at h₂₃
      have hs₂ : (s₂ : R) ≠ 0 := hS s₂
      have key : (r₁ * ↑s₃ - r₃ * ↑s₁) * ↑s₂ = 0 := by
        linear_combination ↑s₃ * h₁₂ + ↑s₁ * h₂₃
      rcases mul_eq_zero.mp key with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hs₂
  · exact ⟨Localization S, inferInstance, inferInstance, Localization.isLocalization⟩

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
theorem Ch2_theorem_39 (R : Type u) [CommRing R] (S : Submonoid R) :
    -- The s₃-relation is an equivalence relation
    (Equivalence (fun (p q : R × S) =>
      ∃ s₃ : S, (s₃ : R) * (q.1 * (p.2 : R) - (q.2 : R) * p.1) = 0)) ∧
    -- The equivalence classes form the localization R[S⁻¹]: there exists a
    -- localization with a homomorphism R → L, all of S invertible, and universality
    (∃ (L : Type u) (_ : CommRing L) (_ : Algebra R L),
      IsLocalization S L ∧
      -- homomorphism R → L exists (via algebraMap)
      (∃ f : R →+* L, ∀ r, f r = algebraMap R L r) ∧
      -- elements of S are invertible in L
      (∀ s : S, IsUnit (algebraMap R L (s : R)))) := by
  constructor
  · constructor
    · intro ⟨r, s⟩
      exact ⟨⟨1, S.one_mem⟩, by simp [mul_comm, sub_self]⟩
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨s₃, hs₃⟩
      exact ⟨s₃, by linear_combination -hs₃⟩
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
      refine ⟨⟨t₁ * t₂ * s₂,
        S.mul_mem (S.mul_mem t₁.2 t₂.2) s₂.2⟩, ?_⟩
      push_cast
      linear_combination
        ↑t₂ * ↑s₃ * ht₁ + ↑t₁ * ↑s₁ * ht₂
  · exact ⟨Localization S, inferInstance, inferInstance,
      Localization.isLocalization,
      ⟨algebraMap R (Localization S), fun _ => rfl⟩,
      fun s => IsLocalization.map_units (Localization S) s⟩
