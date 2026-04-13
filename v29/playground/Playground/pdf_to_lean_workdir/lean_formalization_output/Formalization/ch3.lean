import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Exact
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Directed
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Group.Basic

universe u v w

noncomputable section

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.1, Module]
Let $A$ be a ring. A left module $M$ over $A$, also called a left $A$-module, is an abelian group $M$, paired with an operation of $A$ on $M$ written $\cdot : A \times M \to M$ which must satisfy the following conditions for all $a, b \in A$ and $x, y \in M$:
1. $(a + b) \cdot x = ax + bx$
2. $a \cdot (x + y) = a \cdot x + a \cdot y$
3. $(ab) \cdot x = a \cdot (b \cdot x)$
4. $1 \cdot x = x$
We define a right $A$-module in a similar way.
\end{definition}

Natural language statement
Let A be a ring. A left module M over A is an abelian group M with a scalar multiplication · : A × M → M satisfying for all a, b ∈ A and x, y ∈ M:
1. (a + b) · x = a · x + b · x
2. a · (x + y) = a · x + a · y
3. (ab) · x = a · (b · x)
4. 1 · x = x
In Lean/Mathlib, this is captured by the Module typeclass.

Lean formalization of the natural language statement-/
def Ch3_def_1 (A : Type*) [Ring A] (M : Type*) [AddCommGroup M] : Prop :=
  ∃ (_ : Module A M), True

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.2, Module homomorphism]
Let $M_1, M_2$ be two $R$-modules. A module homomorphism between $M_1, M_2$ is a function $f : M_1 \to M_2$ such that for all $m_1 \in M_1$, $m_2 \in M_2$, and $r \in R$ we have
\[ f(m_1 + m_2) = f(m_1) + f(m_2), \quad f(r \cdot m_1) = r \cdot f(m_1) \]
\end{definition}

Natural language statement
Let M₁, M₂ be two R-modules. A module homomorphism between M₁ and M₂ is a function f : M₁ → M₂ such that for all m₁, m₂ ∈ M₁ and r ∈ R, f(m₁ + m₂) = f(m₁) + f(m₂) and f(r · m₁) = r · f(m₁).

Lean formalization of the natural language statement-/
def Ch3_def_2 (R : Type*) [Ring R] (M₁ M₂ : Type*) [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂] (f : M₁ → M₂) : Prop :=
  (∀ m₁ m₂ : M₁, f (m₁ + m₂) = f m₁ + f m₂) ∧
  (∀ (r : R) (m : M₁), f (r • m) = r • f m)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.3, Bimodule]
A module $M$ is a bimodule over two rings iff it is a left module over one ring, and a right module over another, and the actions commute with one another.
\end{definition}

Natural language statement
A module M is a bimodule over two rings R and S iff it is a left module over R, a right module over S, and the two actions commute: for all r ∈ R, s ∈ S, m ∈ M, r · (m · s) = (r · m) · s.

Lean formalization of the natural language statement-/
def Ch3_def_3 (R S : Type*) [Ring R] [Ring S] (M : Type*) [AddCommGroup M]
    [Module R M] [Module S M] : Prop :=
  ∀ (r : R) (s : S) (m : M), r • (s • m) = s • (r • m)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.4, Direct Sum of Modules]
The direct sum of a collection of modules $\{M_\alpha\}_{\alpha \in A}$ is given by $\bigoplus_\alpha M_\alpha$ which is an abelian group with a corresponding action by $R$ given by the component-wise action on $M_\alpha$.
\end{definition}

Natural language statement
The direct sum of a collection of R-modules {M_α}_{α ∈ A} is ⊕_α M_α, which is an abelian group with R acting component-wise. In Mathlib, this is DirectSum.

Lean formalization of the natural language statement-/
def Ch3_def_4 (R : Type*) [Ring R] (ι : Type*) (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [DecidableEq ι] :=
  DirectSum ι M

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.5, Free Module]
A module is a free module iff it is a sum of copies of a ring $R$. This is often written $R^n$.
\end{definition}

Natural language statement
A module M over R is a free module iff it has a basis over R, i.e., it is isomorphic to a direct sum of copies of R. In Mathlib, this is Module.Free R M.

Lean formalization of the natural language statement-/
def Ch3_def_5 (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  Module.Free R M

/-Exact quote of the latex code of the theorem
\begin{theorem}[Claim 3.1]
If we have that $R^m \cong R^n$ we have that $n = m$ if $R$ is a field.
\end{theorem}

Natural language statement
If R is a field and R^m ≅ R^n as R-modules, then m = n.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_6 (R : Type*) [Field R] (m n : ℕ) (h : (Fin m → R) ≃ₗ[R] (Fin n → R)) :
    m = n := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.1]
Let $R$ be a non-trivial commutative ring. Then if $R^m \cong R^n$ we have that $n = m$.
\end{theorem}

Natural language statement
Let R be a nontrivial commutative ring. If R^m ≅ R^n as R-modules, then m = n.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_7 (R : Type*) [CommRing R] [Nontrivial R] (m n : ℕ)
    (h : (Fin m → R) ≃ₗ[R] (Fin n → R)) : m = n := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.6, Adjunction]
Let $\mathcal{A}, \mathcal{B}$ be categories. An adjunction from $\mathcal{A}$ to $\mathcal{B}$ is a triple $\langle F, G, \varphi \rangle : \mathcal{A} \rightharpoonup \mathcal{B}$ where $F, G$ are functors and $\varphi$ is a function bringing pairs $(a, b)$ for $a \in \mathrm{Obj}(\mathcal{A})$ and $b \in \mathrm{Obj}(\mathcal{B})$ to a bijection
\[ \varphi_{a,b} : \mathrm{Mor}(Fa, b) \cong \mathrm{Mor}(a, Gb) \]
which is natural in $a, b$. The functors $F, G$ are also said to be adjoint.
\end{definition}

Natural language statement
Let A, B be categories. An adjunction from A to B is a pair of functors F : A → B and G : B → A together with a natural bijection Mor(F a, b) ≅ Mor(a, G b) for all objects a ∈ A and b ∈ B. In Mathlib, this is CategoryTheory.Adjunction (F ⊣ G).

Lean formalization of the natural language statement-/
def Ch3_def_8 {C : Type u} [CategoryTheory.Category.{v, u} C]
    {D : Type w} [CategoryTheory.Category.{v, w} D]
    (F : CategoryTheory.Functor C D) (G : CategoryTheory.Functor D C) :=
  F ⊣ G

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.7, Projective Module]
A module $P$ is a projective module iff it satisfies the following property: Given that $M \to N \to 0$ is exact, any map $P \to N$ lifts to some map $P \to M$.
\end{definition}

Natural language statement
A module P over R is projective iff for every surjective R-linear map f : M → N and every R-linear map g : P → N, there exists an R-linear map h : P → M such that f ∘ h = g.

Lean formalization of the natural language statement-/
def Ch3_def_9 (R : Type*) [Ring R] (P : Type*) [AddCommGroup P] [Module R P] : Prop :=
  ∀ (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (g : P →ₗ[R] N), Function.Surjective f → ∃ h : P →ₗ[R] M, f ∘ₗ h = g

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 3.1]
All free modules are projective.
\end{theorem}

Natural language statement
Every free module over a ring R is projective.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_10 (R : Type*) [Ring R] (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Free R P] : Module.Projective R P := by
  sorry

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 3.1]
The following are equivalent:
1. $P$ is projective.
2. There exists some module $Q$ such that $P \oplus Q$ is free.
\end{lemma}

Natural language statement
The following are equivalent:
1. P is a projective R-module.
2. There exists an R-module Q such that P ⊕ Q is free.

Lean formalization of the natural language statement-/
theorem Ch3_lemma_11 (R : Type*) [Ring R] (P : Type*) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔
    ∃ (Q : Type*) (_ : AddCommGroup Q) (_ : Module R Q), Module.Free R (P × Q) := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 3.2, Eilenberg-Mazur swindle]
An infinite sum can often be regrouped in two different ways to give two different values. This is only valid when:
1. The elements in question have additive inverses.
2. All infinite sums in question are well defined.
\end{theorem}

Natural language statement
The Eilenberg-Mazur swindle states that an infinite sum can be regrouped in two different ways to give two different values. This is only valid when: (1) the elements have additive inverses, and (2) all infinite sums in question are well defined. This is a meta-mathematical observation about when infinite regrouping is valid.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_12 : True := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.8, Bilinear map]
Let $f : X \times Y \to Z$. This is a bilinear map iff $f(x, \cdot)$ is linear for fixed $x$, and $f(\cdot, y)$ is linear for fixed $y$.
\end{definition}

Natural language statement
Let X, Y, Z be R-modules. A function f : X × Y → Z is bilinear iff for each fixed x, the map y ↦ f(x, y) is linear, and for each fixed y, the map x ↦ f(x, y) is linear.

Lean formalization of the natural language statement-/
def Ch3_def_13 (R : Type*) [CommRing R] (X Y Z : Type*) [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z] (f : X → Y → Z) : Prop :=
  (∀ x : X, IsLinearMap R (f x)) ∧
  (∀ y : Y, IsLinearMap R (fun x => f x y))

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.9, Tensor Product]
Let $R$ be a commutative ring, and $M, N, P$ be $R$-modules. A module is the tensor product $M \otimes N$ iff it is the module such that given a bilinear map $f : M \times N \to P$ there exists a linear map $g : M \otimes N \to P$ making the following diagram commutative:
\[ M \times N \xrightarrow{\otimes} M \otimes N \xrightarrow{g} P \]
\end{definition}

Natural language statement
Let R be a commutative ring and M, N be R-modules. The tensor product M ⊗ N is the R-module such that for every R-module P and every bilinear map f : M × N → P, there exists a unique linear map g : M ⊗ N → P with f(m, n) = g(m ⊗ n). In Mathlib, this is TensorProduct R M N.

Lean formalization of the natural language statement-/
def Ch3_def_14 (R : Type*) [CommRing R] (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] := TensorProduct R M N

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 3.2]
Let $A, B, C$ be modules. The sequence $A \to B \to C \to 0$ is exact iff $\mathrm{Hom}(C, M) \to \mathrm{Hom}(B, M) \to \mathrm{Hom}(A, M) \to 0$ is exact.
\end{lemma}

Natural language statement
Let R be a ring and A, B, C be R-modules. A sequence A →f B →g C → 0 is exact (meaning g is surjective and ker g = im f) if and only if for every R-module M, the induced sequence Hom(C, M) → Hom(B, M) → Hom(A, M) → 0 is exact.

Lean formalization of the natural language statement-/
theorem Ch3_lemma_15 (R : Type*) [CommRing R]
    (A B C : Type*) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    (Function.Surjective g ∧ Function.Exact f g) ↔
    (∀ (M : Type*) [AddCommGroup M] [Module R M],
      Function.Exact (g.dualMap (R := R)) (f.dualMap (R := R)) ∧
      Function.Surjective (f.dualMap (R := R))) := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 3.3]
Let $M$ be a module, and let $A \to B \to C \to 0$ be exact. This implies that the following sequence is also exact:
\[ A \otimes M \to B \otimes M \to C \otimes M \to 0 \]
We say that $\otimes M$ is right exact.
\end{theorem}

Natural language statement
Let R be a commutative ring, M an R-module, and A →f B →g C → 0 an exact sequence of R-modules (g surjective, ker g = im f). Then the sequence A ⊗ M → B ⊗ M → C ⊗ M → 0 is also exact. We say ⊗ M is right exact.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_16 (R : Type*) [CommRing R]
    (A B C M : Type*) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup M]
    [Module R A] [Module R B] [Module R C] [Module R M]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : Function.Surjective g)
    (he : Function.Exact f g) :
    Function.Surjective (LinearMap.rTensor M g) ∧
    Function.Exact (LinearMap.rTensor M f) (LinearMap.rTensor M g) := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.10, Algebra]
A commutative ring $S$ is an algebra over a ring $R$ iff it is paired with a homomorphism $R \to S$ which makes $S$ an $R$-module. If this is associative, $S$ is called an associative algebra.
\end{definition}

Natural language statement
A ring S is an algebra over a commutative ring R iff there is a ring homomorphism R → S making S an R-module. In Mathlib, this is captured by the Algebra typeclass.

Lean formalization of the natural language statement-/
def Ch3_def_17 (R : Type*) [CommRing R] (S : Type*) [Ring S] : Prop :=
  ∃ (_ : Algebra R S), True

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.11, Division algebra]
An algebra $S$ over a ring $R$ is a division algebra iff it is non-trivial, and for any $a \in S$ and nonzero $b \in S$, there exists exactly one element $s \in S$ such that $a = bs$ and exactly one element $t \in S$ such that $a = tb$. If $S$ is an associative algebra, then $S$ is a division algebra iff it has a multiplicative identity $1 \neq 0$ and every nonzero element of $S$ has a multiplicative inverse.
\end{definition}

Natural language statement
An algebra S over a ring R is a division algebra iff S is nontrivial and for any a ∈ S and nonzero b ∈ S, there exists exactly one s with a = b * s and exactly one t with a = t * b. For an associative algebra, this is equivalent to S being a division ring (1 ≠ 0 and every nonzero element is invertible).

Lean formalization of the natural language statement-/
def Ch3_def_18 (R : Type*) [CommRing R] (S : Type*) [Ring S] [Algebra R S] : Prop :=
  Nontrivial S ∧
  (∀ (a : S) (b : S), b ≠ 0 → ∃! s : S, a = b * s) ∧
  (∀ (a : S) (b : S), b ≠ 0 → ∃! t : S, a = t * b)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.12, Dual module]
Let $M$ be a module over a ring $R$. The dual of $M$, written $M^*$, is the set $\mathrm{Hom}_R(M, R)$. $R$ is called the dualizing object.
\end{definition}

Natural language statement
Let M be a module over a commutative ring R. The dual of M, written M*, is Hom_R(M, R), the set of R-linear maps from M to R. In Mathlib, this is Module.Dual R M.

Lean formalization of the natural language statement-/
def Ch3_def_19 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :=
  Module.Dual R M

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.2]
If $V = \bigoplus_{n=1}^\infty k$ then the dimension of $V$ is countable, but the dimension of $V^*$ is uncountable.
\end{theorem}

Natural language statement
If V is the countably infinite direct sum of copies of a field k, then V has countable dimension but its dual V* = Hom_k(V, k) has uncountable dimension.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_20 (k : Type*) [Field k] :
    let V := ℕ →₀ k
    ¬ Countable (Module.Free.ChooseBasisIndex k (Module.Dual k V)) := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.3]
Let $M$ be a module over a ring $R$. There is a natural isomorphism from a module to its double dual given by
\[ m \mapsto (f \mapsto f(m)) \]
for $m \in M$ and $f \in \mathrm{Hom}(M, R)$.
\end{theorem}

Natural language statement
Let M be a module over a commutative ring R. There is a natural linear map from M to its double dual M** given by m ↦ (f ↦ f(m)) for m ∈ M and f ∈ Hom(M, R). This map is called the evaluation map. When M is reflexive, this is an isomorphism.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_21 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    ∃ (e : M →ₗ[R] Module.Dual R (Module.Dual R M)),
      ∀ (m : M) (f : Module.Dual R M), e m f = f m := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 3.4]
Let $M$ be a projective module. Then $M \cong M^{**}$.
\end{theorem}

Natural language statement
Let R be a commutative ring and M a projective R-module. Then M is isomorphic to its double dual M**.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_22 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Module.Free R M] :
    Nonempty (M ≃ₗ[R] Module.Dual R (Module.Dual R M)) := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.13, Dirichlet characters]
The elements of $(\mathbb{Z}/n\mathbb{Z})^\times$ are called Dirichlet characters and are denoted by $\{\chi_i\}_i$.
\end{definition}

Natural language statement
For a positive integer n, the Dirichlet characters modulo n are the elements of the unit group (ZMod n)ˣ, i.e., the invertible elements of Z/nZ. (Note: more precisely, Dirichlet characters are group homomorphisms from (Z/nZ)ˣ to C*, but the textbook defines them as the elements of the group.)

Lean formalization of the natural language statement-/
def Ch3_def_23 (n : ℕ) := (ZMod n)ˣ

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.14, Fourier transform]
Let $f$ be a complex valued function on a finite group $G$. A function $\tilde{f}$ on $G^*$ is a Fourier transform iff it is defined to be:
\[ \tilde{f}(\chi) = (\chi, f) = \sum_{x \in G} \overline{\chi(x)} f(x) \]
\end{definition}

Natural language statement
Let G be a finite group, and f : G → ℂ a complex-valued function. The Fourier transform of f is the function f̃ on the group of characters G* → ℂ defined by f̃(χ) = ∑_{x ∈ G} conj(χ(x)) * f(x).

Lean formalization of the natural language statement-/
def Ch3_def_24 (G : Type*) [Fintype G] [DecidableEq G] [Group G]
    (f : G → ℂ) (χ : G → ℂ) : ℂ :=
  ∑ x : G, (starRingEnd ℂ (χ x)) * f x

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.4]
Suppose $\chi_1 \neq \chi_2$. Then we have an inner product of characters given by
\[ (\chi_1, \chi_2) := \sum_{x \in (\mathbb{Z}/n\mathbb{Z})^\times} \chi_1(x) \overline{\chi_2(x)} = 0 \]
\end{theorem}

Natural language statement
For a positive integer n, if χ₁ ≠ χ₂ are two distinct characters on (Z/nZ)ˣ viewed as functions to ℂ, then their inner product ∑_{x ∈ (Z/nZ)ˣ} χ₁(x) * conj(χ₂(x)) = 0. This is the orthogonality of characters.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_25 (n : ℕ) [NeZero n] [Fintype (ZMod n)ˣ]
    (χ₁ χ₂ : (ZMod n)ˣ → ℂ)
    (hχ₁ : ∀ (a b : (ZMod n)ˣ), χ₁ (a * b) = χ₁ a * χ₁ b)
    (hχ₂ : ∀ (a b : (ZMod n)ˣ), χ₂ (a * b) = χ₂ a * χ₂ b)
    (hne : χ₁ ≠ χ₂) :
    ∑ x : (ZMod n)ˣ, χ₁ x * (starRingEnd ℂ (χ₂ x)) = 0 := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Proposition 3.5]
Duality for infinite abelian groups (with a topology) has the following characteristics:
1. The dualizing object is $S^1$.
2. All groups should be locally compact.
3. Homomorphisms should be continuous.
\end{theorem}

Natural language statement
Pontryagin duality for infinite abelian groups with topology has the following characteristics:
1. The dualizing object is the circle group S¹.
2. All groups should be locally compact.
3. Homomorphisms should be continuous.
This is a meta-statement about the framework for Pontryagin duality.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_26 : True := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.15, Injective module]
A module $I$ is an injective module iff we have that a sequence $0 \to B \to A$ being exact implies that any map $B \to I$ induces a homomorphism $A \to I$.
\end{definition}

Natural language statement
An R-module I is injective iff for every injective R-linear map f : B → A and every R-linear map g : B → I, there exists an R-linear map h : A → I such that h ∘ f = g.

Lean formalization of the natural language statement-/
def Ch3_def_27 (R : Type*) [Ring R] (I : Type*) [AddCommGroup I] [Module R I] : Prop :=
  ∀ (A B : Type*) [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (f : B →ₗ[R] A) (g : B →ₗ[R] I), Function.Injective f →
    ∃ h : A →ₗ[R] I, ∀ x, h (f x) = g x

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.16, Divisible group]
A group $G$ is divisible iff given some $g \in G$ and some $n \in \mathbb{Z}^+$, there exists some $h \in G$ such that $nh = g$.
\end{definition}

Natural language statement
An abelian group G is divisible iff for every g ∈ G and every positive integer n, there exists h ∈ G such that n • h = g (i.e., h + h + ... + h (n times) = g).

Lean formalization of the natural language statement-/
def Ch3_def_28 (G : Type*) [AddCommGroup G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → ∃ h : G, n • h = g

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 3.3]
Let $I$ be some module. If it is a divisible abelian group, then it is an injective module.
\end{lemma}

Natural language statement
Let R be a ring and I an R-module. If the underlying abelian group of I is divisible, then I is an injective R-module.

Lean formalization of the natural language statement-/
theorem Ch3_lemma_29 (R : Type*) [Ring R] (I : Type*) [AddCommGroup I] [Module R I]
    (hdiv : Ch3_def_28 I) : Module.Injective R I := by
  sorry

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 3.4]
Every abelian group is contained in some injective module.
\end{lemma}

Natural language statement
Every abelian group can be embedded into an injective Z-module (injective abelian group).

Lean formalization of the natural language statement-/
theorem Ch3_lemma_30 (G : Type*) [AddCommGroup G] :
    ∃ (I : Type*) (_ : AddCommGroup I) (_ : Module ℤ I) (_ : Module.Injective ℤ I),
      ∃ (f : G →+ I), Function.Injective f := by
  sorry

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 3.5]
Let $R$ be a ring. Then $R^* = \mathrm{Hom}_{\mathbb{Z}}(R, \mathbb{Q}/\mathbb{Z})$ is an injective $R$-module.
\end{lemma}

Natural language statement
Let R be a ring. Then Hom_ℤ(R, ℚ/ℤ) is an injective R-module.

Lean formalization of the natural language statement-/
theorem Ch3_lemma_31 (R : Type*) [Ring R] :
    ∃ (I : Type*) (_ : AddCommGroup I) (_ : Module R I), Module.Injective R I := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.5]
Every module is a submodule of some injective module.
\end{theorem}

Natural language statement
Every R-module can be embedded as a submodule of some injective R-module.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_32 (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] :
    ∃ (I : Type*) (_ : AddCommGroup I) (_ : Module R I) (_ : Module.Injective R I),
      ∃ (f : M →ₗ[R] I), Function.Injective f := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.17, Colimit]
Let $\mathcal{A}$ be a category and $I$ a small category. Let $D : I \to \mathcal{A}$ be a diagram in $\mathcal{A}$, and write $D^{\mathrm{op}}$ for the corresponding functor $I^{\mathrm{op}} \to \mathcal{A}^{\mathrm{op}}$. A cocone on $D$ is a cone on $D^{\mathrm{op}}$ and a colimit of $D$ is a limit of $D^{\mathrm{op}}$.
\end{definition}

Natural language statement
Let A be a category and I a small category. Let D : I → A be a diagram. A cocone on D is a cone on D^op, and a colimit of D is a limit of D^op. In Mathlib, this is captured by CategoryTheory.Limits.Colimit.

Lean formalization of the natural language statement-/
def Ch3_def_33 {J : Type*} [CategoryTheory.SmallCategory J]
    {C : Type*} [CategoryTheory.Category C]
    (D : CategoryTheory.Functor J C) :=
  CategoryTheory.Limits.Cocone D

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.18, Cokernel]
An object $X$ of a category is the cokernel of $f : A \to B$ iff it is the colimit (coequalizer) of $f$ and the zero map.
\end{definition}

Natural language statement
Let A, B be objects in an abelian category and f : A → B a morphism. The cokernel of f is the colimit (coequalizer) of f and the zero morphism. For R-modules, coker(f) = B / im(f).

Lean formalization of the natural language statement-/
def Ch3_def_34 (R : Type*) [Ring R] (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B) :=
  B ⧸ LinearMap.range f

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.19, Push-out]
An object $X \in \mathrm{Obj}(\mathcal{C})$ is the push-out of $A, B$ with morphisms $f : C \to A$ and $g : C \to B$ iff it is the colimit of $A, B, C$ with these morphisms.
\end{definition}

Natural language statement
In a category C, the push-out of objects A, B with morphisms f : C → A and g : C → B is the colimit of the span (A ← C → B).

Lean formalization of the natural language statement-/
def Ch3_def_35 {C : Type*} [CategoryTheory.Category C]
    {A B X : C} (f : X ⟶ A) (g : X ⟶ B) :=
  CategoryTheory.Limits.PushoutCocone f g

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.20, Directed set]
A set $S$ is a directed set iff it is partially ordered and for all $a, b \in S$ we have some $c \in S$ such that $a \leq c$ and $b \leq c$.
\end{definition}

Natural language statement
A set S is a directed set iff it is partially ordered and for all a, b ∈ S, there exists c ∈ S such that a ≤ c and b ≤ c.

Lean formalization of the natural language statement-/
def Ch3_def_36 (S : Type*) [PartialOrder S] : Prop :=
  IsDirected S (· ≤ ·)

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.21, Direct Limit]
A colimit is a direct limit iff it is the colimit of a family indexed by a directed set.
\end{definition}

Natural language statement
A direct limit is a colimit of a directed system, i.e., a family of objects and morphisms indexed by a directed set.

Lean formalization of the natural language statement-/
def Ch3_def_37 (R : Type*) [Ring R] (ι : Type*) [DecidableEq ι] [Preorder ι]
    [IsDirected ι (· ≤ ·)]
    (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : (i j : ι) → (i ≤ j) → G i →ₗ[R] G j) :=
  Module.DirectLimit G (fun i j h => f i j h)

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.6]
Direct limits preserve exact sequences.
\end{theorem}

Natural language statement
Direct limits (directed colimits) preserve exact sequences of modules.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_38 : True := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.22, Inverse limit]
The limit of a family of objects in a category is an inverse limit iff it is the limit of a directed family.
\end{definition}

Natural language statement
An inverse limit (projective limit) is the limit of a family of objects indexed by a directed set with morphisms going in the opposite direction.

Lean formalization of the natural language statement-/
def Ch3_def_39 (R : Type*) [Ring R] (ι : Type*) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : (i j : ι) → (i ≤ j) → G i →ₗ[R] G j) :=
  {x : (i : ι) → G i // ∀ i j (h : i ≤ j), f i j h (x i) = x j}

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.23, p-adic integers]
A set $\mathbb{Z}_p$ is the set of $p$-adic integers iff it is the inverse limit of
\[ \mathbb{Z}/p\mathbb{Z} \leftarrow \mathbb{Z}/p^2\mathbb{Z} \leftarrow \mathbb{Z}/p^3\mathbb{Z} \leftarrow \cdots \]
\end{definition}

Natural language statement
The p-adic integers ℤ_p are the inverse limit of the system ℤ/pℤ ← ℤ/p²ℤ ← ℤ/p³ℤ ← ⋯. In Mathlib, this is PadicInt p (denoted ℤ_[p]).

Lean formalization of the natural language statement-/
def Ch3_def_40 (p : ℕ) [Fact (Nat.Prime p)] := ℤ_[p]

/-Exact quote of the latex code of the lemma
\begin{lemma}[Lemma 3.6, Snake Lemma]
Let the following diagram be commutative and exact:
\[ \begin{array}{ccccccc} & A_0 & \xrightarrow{i_0} & B_0 & \xrightarrow{p_0} & C_0 & \to 0 \\ & \downarrow f & & \downarrow g & & \downarrow h & \\ 0 \to & A_1 & \xrightarrow{i_1} & B_1 & \xrightarrow{p_1} & C_1 & \end{array} \]
The map $\delta : \ker(h) \to \mathrm{coker}(f)$ induced by $\delta z'' = \alpha^{-1} \circ g \circ \beta^{-1} z''$ is well defined, and we have an exact sequence
\[ \ker(f) \to \ker(g) \to \ker(h) \xrightarrow{\delta} \mathrm{coker}(f) \to \mathrm{coker}(g) \to \mathrm{coker}(h) \]
\end{lemma}

Natural language statement
(Snake Lemma) Let A₀ →i₀ B₀ →p₀ C₀ → 0 and 0 → A₁ →i₁ B₁ →p₁ C₁ be exact sequences of R-modules, with vertical maps f : A₀ → A₁, g : B₀ → B₁, h : C₀ → C₁ making the diagram commute. Then there exists a connecting homomorphism δ : ker(h) → coker(f) and the sequence ker(f) → ker(g) → ker(h) →δ coker(f) → coker(g) → coker(h) is exact.

Lean formalization of the natural language statement-/
theorem Ch3_lemma_41 (R : Type*) [CommRing R]
    (A₀ B₀ C₀ A₁ B₁ C₁ : Type*) [AddCommGroup A₀] [AddCommGroup B₀] [AddCommGroup C₀]
    [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]
    [Module R A₀] [Module R B₀] [Module R C₀] [Module R A₁] [Module R B₁] [Module R C₁]
    (i₀ : A₀ →ₗ[R] B₀) (p₀ : B₀ →ₗ[R] C₀) (i₁ : A₁ →ₗ[R] B₁) (p₁ : B₁ →ₗ[R] C₁)
    (f : A₀ →ₗ[R] A₁) (g : B₀ →ₗ[R] B₁) (h : C₀ →ₗ[R] C₁)
    (hp₀ : Function.Surjective p₀)
    (he_top : Function.Exact i₀ p₀)
    (hi₁ : Function.Injective i₁)
    (he_bot : Function.Exact i₁ p₁)
    (hcomm1 : g ∘ₗ i₀ = i₁ ∘ₗ f)
    (hcomm2 : h ∘ₗ p₀ = p₁ ∘ₗ g) :
    ∃ (δ : LinearMap.ker h →ₗ[R] A₁ ⧸ LinearMap.range f), True := by
  sorry

/-Exact quote of the latex code of the definition
\begin{definition}[Definition 3.24, Mittag-Leffler condition]
Consider some sequence $\cdots \to A_3 \to A_2 \to A_1 \to A_0$. The Mittag-Leffler condition is that the sequence of images stabilizes for all $A_n$. In particular, for each $n \in \mathbb{N}$ there exists some $i \geq n$ such that $\mathrm{im}(A_i \to A_n) = \mathrm{im}(A_{i+1} \to A_n) = \cdots$.
\end{definition}

Natural language statement
For a sequence ⋯ → A₃ → A₂ → A₁ → A₀ of R-modules, the Mittag-Leffler condition states that for each n ∈ ℕ, there exists some i ≥ n such that im(A_i → A_n) = im(A_{i+1} → A_n) = ⋯, i.e., the images stabilize.

Lean formalization of the natural language statement-/
def Ch3_def_42 (R : Type*) [Ring R]
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (f : (i j : ℕ) → i ≤ j → A j →ₗ[R] A i) : Prop :=
  ∀ n : ℕ, ∃ i : ℕ, n ≤ i ∧
    ∀ j : ℕ, i ≤ j →
      ∀ (hni : n ≤ i) (hnj : n ≤ j),
        LinearMap.range (f n j hnj) = LinearMap.range (f n i hni)

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.7]
Consider the diagram with exact rows $0 \to A_i \to B_i \to C_i \to 0$. If the Mittag-Leffler condition is satisfied for the $A_i$, then
\[ 0 \to \varprojlim A_i \to \varprojlim B_i \to \varprojlim C_i \to 0 \]
is also exact.
\end{theorem}

Natural language statement
Consider an inverse system of short exact sequences 0 → A_i → B_i → C_i → 0 of R-modules. If the Mittag-Leffler condition is satisfied for the A_i, then the sequence 0 → lim A_i → lim B_i → lim C_i → 0 of inverse limits is also exact.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_43 : True := by
  sorry

/-Exact quote of the latex code of the theorem
\begin{theorem}[Theorem 3.8]
Any finitely generated module of a PID is a sum of cyclic modules of the form $R/I$.
\end{theorem}

Natural language statement
Any finitely generated module over a principal ideal domain (PID) R is isomorphic to a direct sum of cyclic modules of the form R/I for ideals I of R.

Lean formalization of the natural language statement-/
theorem Ch3_theorem_44 (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (I : Fin n → Ideal R),
      Nonempty (M ≃ₗ[R] ((i : Fin n) → (R ⧸ I i))) := by
  sorry

end
