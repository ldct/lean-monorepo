import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Units.Equiv

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.1, Concrete group]
A set $G$ is a group iff it is the set of symmetries of something.
\end{definition}

Natural language statement
A set G is a concrete group iff it is the set of symmetries of something. Formally, G is a concrete group if there exists a type S and an injective group homomorphism from G into the group of permutations of S.

Lean formalization of the natural language statement-/
def Ch1_def_1 (G : Type*) [Group G] : Prop :=
  ∃ (S : Type*), ∃ (f : G →* Equiv.Perm S), Function.Injective f

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.2, Abstract group]
A set $G$ with a binary relation (if $a, b \in G$, written $a \times b$, $a + b$, $a \cdot b$, $a \circ b$ or just $ab$) is a group iff this relation is associative, each element has an inverse, and there is an identity. In other words, for all $a, b, c \in G$,
1. There exists $e \in G$ such that $ea = ae = a$
2. There exists $a^{-1} \in G$ such that $aa^{-1} = a^{-1}a = e$
3. $a(bc) = (ab)c$
\end{definition}

Natural language statement
A set G with a binary operation is an abstract group iff the operation is associative, each element has an inverse, and there is an identity. That is, for all a, b, c ∈ G:
1. There exists e ∈ G such that ea = ae = a
2. There exists a⁻¹ ∈ G such that aa⁻¹ = a⁻¹a = e
3. a(bc) = (ab)c

Lean formalization of the natural language statement-/
def Ch1_def_2 (G : Type*) [Mul G] : Prop :=
  (∃ e : G, (∀ a : G, e * a = a ∧ a * e = a) ∧
    (∀ a : G, ∃ a_inv : G, a * a_inv = e ∧ a_inv * a = e)) ∧
  (∀ a b c : G, a * (b * c) = (a * b) * c)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.3, Subgroup]
Let $G$ be a group. A subset $H \subseteq G$ is a subgroup of $G$ iff it contains the identity of $G$, is closed under the law of composition, and contains all inverses.
\end{definition}

Natural language statement
Let G be a group. A subset H ⊆ G is a subgroup of G iff it contains the identity of G, is closed under the group operation, and contains all inverses.

Lean formalization of the natural language statement-/
def Ch1_def_3 (G : Type*) [Group G] (H : Set G) : Prop :=
  (1 : G) ∈ H ∧
  (∀ a b : G, a ∈ H → b ∈ H → a * b ∈ H) ∧
  (∀ a : G, a ∈ H → a⁻¹ ∈ H)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.4, Homomorphism]
Let $G, H$ be two groups. Then a function $f : G \to H$ is a homomorphism iff for all $a, b \in G$,
\[ f(ab) = f(a)f(b) \]
\end{definition}

Natural language statement
Let G, H be two groups. A function f : G → H is a homomorphism iff for all a, b ∈ G, f(ab) = f(a)f(b).

Lean formalization of the natural language statement-/
def Ch1_def_4 (G H : Type*) [Group G] [Group H] (f : G → H) : Prop :=
  ∀ a b : G, f (a * b) = f a * f b

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 1.1]
Homomorphisms preserve inverses and the identity.
\end{theorem}

Natural language statement
If f : G → H is a group homomorphism, then f preserves the identity (f(e) = e) and f preserves inverses (f(a⁻¹) = f(a)⁻¹ for all a ∈ G).

Lean formalization of the natural language statement-/
theorem Ch1_theorem_5 (G H : Type*) [Group G] [Group H] (f : G →* H) :
    f 1 = 1 ∧ ∀ g : G, f g⁻¹ = (f g)⁻¹ := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.5, Isomorphism]
A homomorphism is an isomorphism iff it is a bijection.
\end{definition}

Natural language statement
A group homomorphism f : G → H is an isomorphism iff f is a bijection.

Lean formalization of the natural language statement-/
def Ch1_def_6 (G H : Type*) [Group G] [Group H] (f : G →* H) : Prop :=
  Function.Bijective f

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.6, Endomorphism]
A homomorphism is an endomorphism iff it has the same domain as its codomain.
\end{definition}

Natural language statement
A group homomorphism is an endomorphism iff it has the same domain as its codomain, i.e., it is a homomorphism from G to G.

Lean formalization of the natural language statement-/
def Ch1_def_7 (G : Type*) [Group G] := G →* G

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.7, Automorphism]
A homomorphism is an automorphism iff it is an isomorphism and an endomorphism.
\end{definition}

Natural language statement
A group homomorphism is an automorphism iff it is both an isomorphism (bijective) and an endomorphism (domain equals codomain), i.e., it is a bijective homomorphism from G to G.

Lean formalization of the natural language statement-/
def Ch1_def_8 (G : Type*) [Group G] := G ≃* G

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.8, Left action]
Let $G$ be a group and $S$ a set. Then a map $\cdot : G \times S \to S$ is a left action of $G$ on $S$ iff for all $s \in S$ and all $g, h \in G$ we have:
1. $g \cdot (h \cdot s) = (gh) \cdot s$
2. $e \cdot s = s$
where $e$ is the identity for $G$. A right action is a map $\cdot : S \times G \to S$ which satisfies the analogous properties.
\end{definition}

Natural language statement
Let G be a group and S a set. A map · : G × S → S is a left action of G on S iff for all s ∈ S and all g, h ∈ G:
1. g · (h · s) = (gh) · s
2. e · s = s
where e is the identity element of G.

Lean formalization of the natural language statement-/
def Ch1_def_9 (G : Type*) [Group G] (S : Type*) (smul : G → S → S) : Prop :=
  (∀ g h : G, ∀ s : S, smul g (smul h s) = smul (g * h) s) ∧
  (∀ s : S, smul 1 s = s)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 1.9, G-set]
Let $G$ be a group. A set $S$ is a $G$-set iff we have an action of $G$ on $S$ which is a homomorphism
\[ \pi : G \to \mathrm{Perm}(S) \]
\end{definition}

Natural language statement
Let G be a group. A set S is a G-set iff there exists a group homomorphism π : G → Perm(S) from G to the group of permutations of S.

Lean formalization of the natural language statement-/
def Ch1_def_10 (G : Type*) [Group G] (S : Type*) : Prop :=
  ∃ (_ : G →* Equiv.Perm S), True

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 1.1]
A set $G$ is an abstract group iff it is a concrete group.
\end{theorem}

Natural language statement
A set G is an abstract group if and only if it is a concrete group. That is, every abstract group can be realized as a group of permutations (Cayley's theorem), and conversely every group of permutations is an abstract group.

Lean formalization of the natural language statement-/
theorem Ch1_theorem_11 (G : Type*) [Group G] : Ch1_def_1 G := by
  sorry
