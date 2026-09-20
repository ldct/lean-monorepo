import Mathlib

-- API guide to J. S. Milne, Group Theory, v4.01 (2025), Mathlib v4.32.0.
-- Numbered comments follow the PDF; #check displays the full hypotheses and conclusion.
-- RELATED means building blocks, not a formalization of the entire cited statement.
-- GAP means no matching result was located in this Mathlib version, not a proof of absence.
-- This includes unassembled examples/calculations and particular proof methods;
-- a GAP does not necessarily require new definitions or new general theorems.
-- Examples/exercises with GAP still have their mathematical content recorded below.
-- Conventions: Nat.card and orderOf use 0 for infinity; IsSimpleGroup excludes the trivial group.

-- Chapter 1. Basic definitions and results.

-- Source: https://www.jmilne.org/math/CourseNotes/GT.pdf
-- Source-derived comments: CC BY-NC-SA 4.0, https://creativecommons.org/licenses/by-nc-sa/4.0/.

-- Definition 1.1, a group

#check AddGroup
#check Group

-- 1.2(a,b): uniqueness of the identity and inverse.
#check mul_eq_left
#check inv_eq_of_mul_eq_one_left
#check inv_eq_of_mul_eq_one_right
-- 1.2(c,d): ordered products and reversal under inversion.
#check List.prod_append
#check List.prod_inv_reverse
-- 1.2(e): cancellation; finite cancellative monoids are groups.
#check mul_left_cancel_iff
#check mul_right_cancel_iff
#check LeftCancelMonoid.groupOfFinite
#check RightCancelMonoid.groupOfFinite


-- Two groups are called isomorphic if there exists a bijective homomorphism between them.
-- In lean: the type of isomorphisms between two groups.
variable (G : Type*) [Group G] (H : Type*) [Group H] in
#check G ≃* H

-- The order of a group is the number of elements in the group.
-- In lean: the cardinality of the type.
variable (G : Type*) [Group G] in
#check Nat.card G

-- A finite p-group has order a power of the prime p.
-- In lean: IsPGroup also applies to infinite groups; include finiteness here.
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G] in
#check IsPGroup p G

-- Integer powers of a group element (page 8).
-- In lean: the exponent type distinguishes integer powers from natural powers.
variable (G : Type*) [Group G] (a : G) (n : ℤ) in
#check a ^ n

-- The power laws in equation (4).
-- In lean: zpow_add and zpow_mul express these identities for integer exponents.
variable (G : Type*) [Group G] (a : G) (m n : ℤ) in
#check zpow_add a m n
variable (G : Type*) [Group G] (a : G) (m n : ℤ) in
#check zpow_mul a m n

-- The order of an element is its least positive exponent giving the identity, or zero
-- when the element has infinite order.
variable (G : Type*) [Group G] (a : G) in
#check orderOf a

-- Example 1.3: the additive cyclic groups ℤ and ℤ/mℤ, for m ≥ 1.
-- In lean: ZMod m is the integers modulo m; NeZero excludes m = 0.
#synth AddGroup ℤ
variable (m : ℕ) [NeZero m] in
#synth AddGroup (ZMod m)

-- 1.4: permutations and the order of the symmetric group.
#check Equiv.Perm
#check Equiv.Perm.mul_apply
#check Fintype.card_perm
-- 1.5: direct products.
variable (G H : Type*) [Group G] [Group H] in
#synth Group (G × H)

-- 1.6: abelian groups, unordered products, integer scalar multiplication, torsion.
#check CommGroup
#check AddCommGroup
#check Finset.prod
#check add_zsmul
#check mul_zsmul
#check zsmul_add
#check AddCommGroup.toIntModule
#check AddCommGroup.torsion

-- 1.7: general linear groups and change from linear maps to matrices.
#check Matrix.GeneralLinearGroup
#check LinearMap.GeneralLinearGroup
#check Matrix.GeneralLinearGroup.toLin'

-- 1.8: bilinear forms, isometries, orthogonal and symplectic groups.
#check LinearMap.BilinForm
#check LinearMap.BilinForm.IsometryEquiv
#check Matrix.orthogonalGroup
#check Matrix.symplecticGroup
-- GAP: no single API found for Milne's full basis-normalization argument here.
-- In particular, the change-of-basis reduction of a bilinear form to the
-- standard symmetric/skew, orthogonal, or symplectic normal forms is not exposed
-- as one theorem connecting `BilinForm.IsometryEquiv` with `Matrix.orthogonalGroup`.
-- Caution: in characteristic 2, skew-symmetric need not mean alternating.

-- 1.9: magmas, semigroups, monoids and empty products.
#check Mul
#check Semigroup
#check Monoid
#check List.prod_nil
-- 1.10: one-sided group axioms; RELATED for the minimal-axiom counterexamples.
#check Group.ofLeftAxioms

-- Multiplication tables (p. 12): each row/column is a permutation.
#check Equiv.mulLeft
#check Equiv.mulRight
-- 1.11: subgroups; closure under multiplication and inverses.
#check Subgroup
#check Subgroup.mk
-- 1.12: the centre.
#check Subgroup.center
#check Subgroup.mem_center_iff
-- 1.13, 1.14: arbitrary intersections of subobjects.
variable (G : Type*) [Group G] in
#synth CompleteLattice (Subgroup G)
#check Subgroup.mem_iInf
#check Subring.mem_iInf
#check Submodule.mem_iInf
-- 1.15: generated subgroups and their minimality.
#check Subgroup.closure
#check Subgroup.closure_le
#check Subgroup.closure_induction
-- 1.16: cyclic groups, finite and infinite classification.
#check IsCyclic
#check Subgroup.zpowers
#check zmodCyclicMulEquiv
#check intCyclicMulEquiv
#check orderOf_dvd_iff_pow_eq_one
#check orderOf_dvd_iff_zpow_eq_one
-- 1.17: D_n has order 2n; n = 0 gives the infinite dihedral group.
#check DihedralGroup
#check DihedralGroup.card
#check DihedralGroup.r
#check DihedralGroup.sr
-- 1.18: Q_8 is QuaternionGroup 2 (Mathlib's parameter gives order 4n).
#check QuaternionGroup 2
#check QuaternionGroup.card
#check QuaternionGroup.xa_sq

-- 1.19: transpositions, sign, alternating groups.
#check Equiv.swap
#check Equiv.Perm.closure_isSwap
#check Equiv.Perm.sign
#check alternatingGroup
-- Groups of small order (p. 15): GAP for the complete enumeration table through order 16.
-- RELATED: cyclic/dihedral/quaternion constructions above and prime-order classification below.
-- The missing result is an isomorphism-free list of every group of each order
-- 1 through 16, including the counts and names (for example the five groups of
-- order 8), rather than constructors for selected families.

-- 1.20: group homomorphisms (Mathlib calls these MonoidHom).
variable (G H : Type*) [Group G] [Group H] in
#check G →* H
#check MulEquiv.ofBijective
#check Matrix.GeneralLinearGroup.det
-- 1.21: homomorphisms preserve products, identities, inverses and powers.
#check map_list_prod
#check map_one
#check map_inv
#check map_zpow
-- 1.22, 1.23: Cayley's embedding; relabel a finite G with Fin (Nat.card G).
variable (G : Type*) [Group G] in
#check MulAction.toPermHom G G
#check MulAction.toPerm_injective
#check Fintype.equivFin
#check Equiv.permCongr
-- Cosets and 1.24: translated subsets; affine subspaces supply the geometric example.
open scoped Pointwise
variable (G : Type*) [Group G] (a : G) (H : Subgroup G) in
#check a • (H : Set G)
#check AffineSubspace
-- 1.25: membership, equality and equipotence of cosets.
#check mem_leftCoset_iff
#check leftCoset_eq_iff
#check Subgroup.leftCosetEquivSubgroup
#check Subgroup.groupEquivQuotientProdSubgroup
-- 1.26, 1.27: index, Lagrange, and the order of an element.
#check Subgroup.index
#check Subgroup.index_mul_card
#check Subgroup.card_subgroup_dvd_card
#check orderOf_dvd_natCard
-- 1.28: groups of prime order are cyclic.
#check isCyclic_of_prime_card
#check mulEquivOfPrimeCardEq
-- 1.29: right cosets; inversion exchanges left and right cosets.
#check Subgroup.rightCosetEquivSubgroup
-- 1.30: partial converses to Lagrange (see also 4.13 and 5.2).
#check exists_prime_orderOf_dvd_card'
#check Sylow.exists_subgroup_card_pow_prime
-- GAP: the specific C2 × C2 and A4 counterexamples are not packaged here.
-- The partial converse only guarantees an element of order p for prime p and a
-- subgroup of order p^n by Sylow. The examples show the limits: V₄ has order 4
-- but no element of order 4, while A₄ has order 12 but no subgroup of order 6.
-- 1.31: multiplicativity of index in a subgroup tower.
#check Subgroup.relIndex_mul_index
-- 1.32: normality as closure under conjugation.
#check Subgroup.Normal
#check Subgroup.Normal.conj_mem
-- 1.33: GAP: the GL2(Q) example with gHg⁻¹ strictly contained in H.
-- What is missing is a concrete infinite-group witness: a subgroup H ≤ GL₂(Q)
-- and an explicit g with gHg⁻¹ ⊊ H, showing that conjugate subgroups can have
-- proper containment even though conjugation is an ambient automorphism.
-- 1.34, 1.35: normality is equality of left and right cosets.
#check normal_iff_eq_cosets
-- 1.36: index two implies normality; abelian subgroups are normal.
#check Subgroup.normal_of_index_eq_two
variable (G : Type*) [CommGroup G] (H : Subgroup G) in
#synth H.Normal
#check IsSimpleGroup
-- GAP: Q8's every-subgroup-normal counterexample is not packaged in Quaternion.lean.
-- The intended finite example is that every subgroup of Q₈ is normal while Q₈
-- is nonabelian; the nearby abelian theorem only gives the easy direction that
-- every subgroup of an abelian group is normal.
-- 1.37: products with normal subgroups are joins; normal joins are normal.
#check Subgroup.mem_sup_of_normal_right
variable (G : Type*) [Group G] (H N : Subgroup G) [H.Normal] [N.Normal] in
#synth (H ⊔ N).Normal
-- 1.38, 1.39, 1.40: conjugation closure and normal closure.
#check Group.conjugatesOfSet
#check Group.conj_mem_conjugatesOfSet
#check Subgroup.normalClosure
#check Subgroup.normalClosure_le_normal
#check Subgroup.normalizer_le_normalizer_closure
-- 1.38 follows by specializing this to a conjugation-stable generating set.

-- 1.41: kernels are normal; injectivity is equivalent to trivial kernel.
#check MonoidHom.ker
#check MonoidHom.ker_eq_bot_iff
variable (G H : Type*) [Group G] [Group H] (f : G →* H) in
#synth f.ker.Normal
#check Matrix.SpecialLinearGroup
-- 1.42: quotient group and its projection kernel.
variable (G : Type*) [Group G] (N : Subgroup G) [N.Normal] in
#synth Group (G ⧸ N)
#check QuotientGroup.mk'
#check QuotientGroup.ker_mk'
-- 1.43: quotient universal property, including uniqueness.
#check QuotientGroup.lift
#check QuotientGroup.lift_comp_mk'
#check QuotientGroup.monoidHom_ext
-- 1.44: RELATED: cyclic quotients; vector-space and dihedral examples require specialization.
#check Int.quotientZMultiplesNatEquivZMod
-- 1.45: first isomorphism theorem.
#check QuotientGroup.quotientKerEquivRange
-- 1.46: second isomorphism theorem.
#check QuotientGroup.quotientInfEquivProdNormalQuotient
-- 1.47, 1.48: correspondence and third isomorphism theorems.
#check QuotientGroup.comapMk'OrderIso
#check QuotientGroup.quotientQuotientEquivQuotient
-- 1.49: GAP: explicit D4 and D4/⟨r²⟩ subgroup diagrams.
-- The missing artifact is the concrete subgroup lattice, with inclusions,
-- normality labels, and the quotient map identifying D₄/⟨r²⟩ with the Klein
-- four group (the general quotient/isomorphism APIs are present above).
-- 1.50, 1.51: internal direct products via normal complementary subgroups.
#check Subgroup.IsComplement'
#check Subgroup.IsComplement'.QuotientMulEquiv
-- RELATED: combine the complement equivalence with the product constructions below.
-- 1.52: RELATED: the multiplication map for pairwise commuting subgroups,
-- its image, and injectivity for independent subgroups encode the finite-family version.
#check Subgroup.noncommPiCoprod
#check Subgroup.noncommPiCoprod_range
#check Subgroup.injective_noncommPiCoprod_of_iSupIndep
#check DirectSum.IsInternal
-- 1.53: GAP: the prescribed primitive integer combination of a generating family.
-- This is the constructive Bézout-style statement that if x₁,…,xₖ generate an
-- abelian group and gcd(c₁,…,cₖ)=1, then one can replace the generating family
-- by generators y₁,…,yₖ whose first member is Σ cᵢxᵢ.
-- 1.54: finitely generated abelian groups are sums of cyclic groups.
#check AddCommGroup.equiv_free_prod_directSum_zmod
-- 1.55: a bound on n-torsion implies cyclicity.
#check isCyclic_of_card_pow_eq_one_le
-- 1.56: finite multiplicative subgroups of fields are cyclic.
#check isCyclic_of_subgroup_isDomain
-- 1.57, 1.58: primary decomposition of finitely generated / finite abelian groups.
#check AddCommGroup.equiv_directSum_zmod_of_finite
#check CommGroup.equiv_free_prod_prod_multiplicative_zmod
-- RELATED: existence of primary factors; GAP for the full invariant-factor uniqueness
-- statement and the explicit order-90 classification as a single ready-made API.
-- The missing uniqueness theorem compares two decompositions by divisibility of
-- invariant factors, while the order-90 example would instantiate it to a
-- complete list of abelian groups of that order with their invariant factors.
-- Linear characters: circle-valued homomorphisms; additive-domain API is AddChar.
#check Circle
#check AddChar
#check rootsOfUnity
-- 1.59: the quadratic character.
#check legendreSym
#check legendreSym.mul
-- 1.60: finite duality and the evaluation isomorphism.
#check CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
#check AddChar.doubleDualEquiv
-- 1.61: topological dual; GAP: general locally compact Pontryagin duality theorem.
-- `PontryaginDual` names the construction, but no theorem here identifies a
-- locally compact abelian group with its double dual or supplies the full
-- continuous-character duality equivalence, including the required topology.
#check PontryaginDual
-- 1.62, 1.63: orthogonality and summing over the dual group.
#check AddChar.sum_eq_ite
#check AddChar.wInner_cWeight_eq_boole
#check AddChar.sum_apply_eq_ite
-- 1.64: GAP: arbitrary prescribed orders m,n,r > 1 of a,b,ab in a finite group.
-- Missing is the universal existence theorem: for every m,n,r > 1 there is a
-- finite group containing a,b with ord(a)=m, ord(b)=n, and ord(ab)=r; the local
-- `orderOf` checks do not construct the required finite group.

-- Chapter 2. Free groups and presentations; Coxeter groups.

-- Free monoids (p. 31): words, concatenation, empty word and universal property.
#check FreeMonoid
#check FreeMonoid.of
#check FreeMonoid.lift
-- 2.1: reduced words and uniqueness of reduction.
#check FreeGroup
#check FreeGroup.reduce
#check FreeGroup.isReduced_iff_reduce_eq
#check FreeGroup.reduce.sound
#check FreeGroup.reduce.exact
#check FreeGroup.Red.exact
-- 2.2: multiplication respects word equivalence.
#check FreeGroup.mul_mk
-- 2.3, 2.4: universal property (an equivalence) and uniqueness of the extension.
#check FreeGroup.lift
#check FreeGroup.lift_unique
-- 2.5: every group is a quotient of a free group.
#check FreeGroup.prod
#check FreeGroup.prod_surjective
#check QuotientGroup.quotientKerEquivOfSurjective
-- 2.6: Nielsen-Schreier.
#check IsFreeGroup
#check subgroupIsFreeOfIsFree
-- Presentations: generators and relators; the relators generate the kernel normally.
#check PresentedGroup
#check PresentedGroup.mk_eq_one_iff
-- 2.7(a,b), 2.9: RELATED: dihedral and generalized quaternion relations.
#check DihedralGroup.r_mul_r
#check DihedralGroup.sr_mul_sr
#check QuaternionGroup.a_mul_xa
#check QuaternionGroup.xa_mul_xa
-- GAP: the identifications with these exact presentations are not packaged here.
-- In particular, there is no equivalence from the quotient of the free group by
-- the displayed dihedral or generalized-quaternion relators to the named
-- `DihedralGroup`/`QuaternionGroup`, with the normal-form and cardinality proof
-- bundled into the presentation API.
-- Milne's Q_n (order 2^n) corresponds to QuaternionGroup (2^(n-2)), n ≥ 3.
-- 2.8: universal property of a presented group.
#check PresentedGroup.toGroup
#check PresentedGroup.toGroup.unique
-- 2.10(a): free product C_m * C_n; RELATED for the infinite order of xy.
#check Monoid.Coprod
#check PresentedGroup.coprodPresentations
-- 2.10(b): GAP: PSL2(Z) ≃ C2 * C3 and its stated simple quotients.
-- The missing concrete calculation identifies the modular group with the free
-- product of cyclic groups of orders 2 and 3, then identifies the relevant
-- finite quotients and proves their simplicity; generic constructors do not.
-- 2.11: all finite groups are finitely presented.
#check Group.IsFinitelyPresented
variable (G : Type*) [Group G] [Finite G] in
#synth Group.IsFinitelyPresented G
-- Word problem / Burnside problem (p. 37): GAP: general undecidability and the
-- Novikov-Adian, Golod-Shafarevich, and restricted Burnside results cited here.
-- Mathlib has decidable equality for a free group and an exponent operation,
-- but no general theorem here about undecidability of the word problem, the
-- existence of infinite finitely generated groups of fixed exponent, or the
-- restricted-Burnside finiteness theorem.
-- RELATED: free-group word equality is decidable; group exponent is available.
variable (X : Type*) [DecidableEq X] in
#synth DecidableEq (FreeGroup X)
#check Monoid.exponent
-- Todd-Coxeter algorithm: GAP: no verified coset-enumeration implementation located.
-- The missing computational API would accept finite generators/relators and a
-- subgroup presentation, perform coset-table deductions, and return an index
-- together with a correctness certificate; quotient groups alone do not do this.

-- Coxeter matrices: Mathlib uses 0 for ∞, not WithTop ℕ.
#check CoxeterMatrix
#check CoxeterMatrix.Group
#check CoxeterSystem
#check IsCoxeterGroup
-- 2.12, 2.13: rank-one / rank-two systems; RELATED: type A and dihedral matrices.
#check CoxeterMatrix.A
#check CoxeterMatrix.I
-- GAP: the rank-one/rank-two classification is not provided by these constructors.
-- What is absent is the theorem that rank one gives the order-two Coxeter group
-- and rank two gives the finite dihedral group when m < ∞ (and the corresponding
-- infinite case), including uniqueness from the Coxeter matrix.
-- 2.14: reflections; GAP: equivalence of finite reflection groups and finite Coxeter groups.
-- The missing bridge turns a faithful finite real reflection representation into
-- a Coxeter system and conversely realizes a finite Coxeter group by reflections;
-- `Module.reflection` only constructs individual linear maps.
#check Module.reflection
-- 2.15: RELATED: permutation and dihedral groups above; GAP for the concrete reflection realizations.
-- In particular, no checked matrices/vectors are supplied for the standard
-- A-type permutation representation or rank-two dihedral reflection group,
-- with the generated group identified with its Coxeter presentation.
-- 2.16: the defining involution and braid-order relations are available.
#check CoxeterSystem.simple_mul_simple_self
#check CoxeterSystem.simple_mul_simple_pow
-- GAP: these equations alone do not prove injectivity of simple generators or exact orders.
-- The missing consequences are that each simple generator is genuinely a
-- distinct involution in the presented group and that adjacent-generator
-- products have exactly the prescribed order, rather than only satisfying it.
-- 2.17, 2.18: GAP: the geometric representation's rank-two form and exact rotation order.
-- Missing are the explicit bilinear form and reflection matrices for rank two,
-- followed by the calculation that the product is a rotation of exact order m
-- (or infinite order when the Coxeter entry is 0).
-- 2.19: GAP: faithfulness of the geometric representation.
-- The absent theorem says that the geometric representation has trivial kernel
-- (equivalently, the canonical map to the generated reflection group is
-- injective), which is stronger than merely having a representation.

-- Chapter 3. Automorphisms and extensions.

-- Automorphism group, inner automorphisms and outer automorphisms (pp. 43-44).
#check MulAut
#check MulAut.conj
-- RELATED: Inn(G) is the range of conj, Out(G) its quotient in MulAut G.
-- 3.1: RELATED: automorphisms of elementary abelian p-groups are linear automorphisms.
#check LinearEquiv
-- GAP: the explicit Aut(C2 × C2) ≃ S3 identification is not packaged here.
-- The missing equivalence sends the three nonidentity elements of the Klein
-- four group to a permutation of those elements, proving Aut(V₄) has order 6
-- and is isomorphic to S₃; `LinearEquiv` supplies only the general language.
-- 3.2: GAP: Schupp's characterization of inner automorphisms by extendibility.
-- The precise missing converse says that an automorphism of H which extends to
-- an automorphism of every overgroup G containing H must be inner; the forward
-- direction is immediate because conjugation by an element of H extends to G.
-- `MulAut.conj` only describes the inner automorphisms themselves.
-- 3.3: complete groups can be expressed directly by bijectivity of conjugation.
variable (G : Type*) [Group G] in
#check Function.Bijective (MulAut.conj : G → MulAut G)
-- 3.4: GAP: completeness of S_n (n ≠ 2,6) and of Aut(G) for nonabelian simple G.
-- Missing are the concrete hypotheses and proofs that Sₙ has trivial centre and
-- only inner automorphisms outside degrees 2 and 6, together with the distinct
-- theorem that Aut(G) itself is complete when G is nonabelian simple.
-- 3.5(a): automorphisms of cyclic groups.
#check IsCyclic.mulAutMulEquiv
-- 3.5(b,c): RELATED: Chinese remainder theorem and units; prime-power unit structure.
#check ZMod.chineseRemainder
#check Units.mapEquiv
#check ZMod.isCyclic_units_of_prime_pow
#check ZMod.orderOf_five
-- GAP: full displayed decomposition of units at powers of 2 not identified here.
-- The missing classification spells out U(2^n) for n ≥ 3 as a product of two
-- cyclic 2-groups, with explicit generators and orders; CRT and prime-power
-- cyclicity do not cover these exceptional 2-power factors.
-- 3.6: characteristic subgroups.
#check Subgroup.Characteristic
-- 3.7: characteristic implies normal; the centre is characteristic.
variable (G : Type*) [Group G] (H : Subgroup G) [H.Characteristic] in
#synth H.Normal
#check Subgroup.centerCharacteristic
#check Subgroup.characteristic_of_characteristic_of_characteristic
#check ConjAct.normal_of_characteristic_of_normal
-- RELATED: characteristic subgroups of normal subgroups and uniqueness-by-order arguments.
-- 3.8: internal semidirect products: normal complementary subgroups.
#check SemidirectProduct.mulEquivSubgroup
-- 3.9: RELATED: D_n = C_n ⋊ C2 and the affine group; specialize the action below.
-- GAP: these example identifications have not been located as standalone equivalences.
-- The intended equivalences identify the dihedral and affine examples with
-- particular semidirect products, including the explicit action on the normal
-- factor; the generic API leaves those maps and cardinality calculations open.
-- 3.10: external semidirect product, multiplication and embeddings.
#check SemidirectProduct
#check SemidirectProduct.mul_def
#check SemidirectProduct.inl
#check SemidirectProduct.inr
-- 3.11: GAP: the nontrivial C3 ⋊ C4 example and its element-order comparison with A4,D6.
-- Missing is the explicit nontrivial action C₄ → Aut(C₃), construction of the
-- resulting group, and proof that its element orders distinguish it from A₄
-- and D₆ despite having the same order.
-- 3.12: the trivial action gives a direct product.
#check SemidirectProduct.mulEquivProd
-- 3.13: RELATED: order-six groups are C6 or D3 (see 4.15).
-- 3.14, 3.15: GAP: the two explicit nonabelian groups of order p³, p odd.
-- The absent classification constructs the two families (the exponent-p
-- Heisenberg group and C_{p²} ⋊ C_p), proves they are nonisomorphic, and shows
-- these exhaust the nonabelian groups of order p³.
-- 3.16: an automorphism becomes inner in a semidirect product with an infinite cyclic group.
#check SemidirectProduct.inl_aut
-- 3.17, 3.18: isomorphisms induced by compatible changes of the two factors.
#check SemidirectProduct.congr
#check SemidirectProduct.congr'
-- 3.19: GAP: conjugate action images for finite cyclic Q imply isomorphic semidirect products.
-- Missing is the classification statement that two actions of a finite cyclic
-- quotient with conjugate images in Aut(N) yield isomorphic semidirect products,
-- together with the explicit isomorphism induced by conjugating the action.
-- 3.20: direct and semidirect products of complementary subgroups; see 1.50 and 3.8.
-- GAP: the Zappa-Szep product (neither factor normal) and the C25 ⋊ Z counterexample
-- showing why 3.19 requires finite Q.
-- The first missing construction factors a group through two mutually
-- complementary nonnormal subgroups. The second is an explicit infinite
-- semidirect product where conjugate action images do not force isomorphism,
-- demonstrating why the finiteness assumption on Q matters.
-- Extensions, equivalence of extensions and splittings (pp. 50-52).
#check GroupExtension
#check GroupExtension.Equiv
#check GroupExtension.Splitting
#check GroupExtension.Splitting.semidirectProductMulEquiv
-- GAP: the two explicit nonsplitting examples (Cp² and Q8) are not packaged here.
-- These are concrete extensions with no subgroup complement: the central
-- extension C_{p²} over C_p and the extension realizing Q₈ over C₂×C₂.
-- `GroupExtension.Splitting` records splitting when supplied, but does not give
-- these obstruction examples.
-- 3.21: Schur-Zassenhaus (existence of a complement to a normal Hall subgroup).
#check Subgroup.exists_right_complement'_of_coprime
-- 3.22: RELATED: centralizers and conjugation action of an extension.
#check Subgroup.centralizer
#check GroupExtension.conjAct
-- GAP: splitting over a complete kernel as a single theorem.
-- The missing theorem says an extension with complete kernel (trivial center
-- and all automorphisms inner) splits, and in fact identifies the extension
-- with the direct product of the kernel and its centralizer, as in Milne's
-- Proposition 3.22; the current extension API does not package that result.
-- Extension classes (p. 52): GAP: the nonabelian Ext¹(Q,N)_θ classification and Baer sum
-- in this formulation; GroupExtension.Equiv records the equivalence relation.
-- In particular, there is no parameterization of extension-equivalence classes
-- by nonabelian cocycles for a fixed outer action, nor the Baer-sum operation on
-- those classes.
-- Hölder program (pp. 52-53): GAP: classification of all finite simple groups,
-- the 26 sporadic groups, and the cited Brauer-Fowler/Feit-Thompson results.
-- These are the large classification and order-theoretic theorems themselves:
-- finite simple groups are partitioned into cyclic, alternating, Lie-type, and
-- 26 sporadic families, with the cited odd-order and bounded-order results.
-- RELATED: cyclic simple groups, alternating simple groups, and projective linear groups.
#check Group.is_simple_iff_prime_card
#check Matrix.ProjectiveSpecialLinearGroup
-- GAP: the cited simplicity theorem for projective special linear groups.
-- Missing is the parameterized theorem giving simplicity of PSL(n,F) under the
-- usual small-rank/field exceptions, plus the quotient from SL to PSL and the
-- exact treatment of exceptional low-dimensional cases.

-- Chapter 4. Groups acting on sets.

-- 4.1: actions, associated permutation homomorphism and faithfulness.
#check MulAction
#check MulAction.toPermHom
#check FaithfulSMul
-- 4.2: translation, quotient, conjugation, automorphism and isometry actions.
#check ConjAct
#check ConjAct.smul_def
#check MulActionHom.toQuotient
#check IsometryEquiv
-- Equivariant maps and equivalences.
#check MulActionHom
variable (G X Y : Type*) [Group G] [MulAction G X] [MulAction G Y] in
#check {f : X →[G] Y // Function.Bijective f}
-- 4.3: orbits, transitivity, homogeneous G-sets; cyclic orbits give permutation cycles.
#check MulAction.orbit
#check MulAction.IsPretransitive
#check MulAction.IsMultiplyPretransitive
#check IsCancelSMul
#check Equiv.Perm.cycleOf
-- Stabilizers and 4.4: stabilizers of points in one orbit are conjugate.
#check MulAction.stabilizer
#check MulAction.stabilizer_smul_eq_stabilizer_map_conj
-- 4.5: conjugation stabilizers are centralizers; RELATED for rigid-motion stabilizers.
#check ConjAct.stabilizer_eq_centralizer
-- 4.6: normalizers, and normality in the normalizer.
#check Subgroup.normalizer
-- 4.7, 4.8: transitive actions and orbit-stabilizer.
#check MulAction.orbitEquivQuotientStabilizer
#check MulAction.card_orbit_mul_card_stabilizer_eq_card_group
-- 4.9, 4.10: the kernel of the coset action is the normal core.
#check Subgroup.normalCore
#check Subgroup.normalCore_eq_iInf_map_conj
#check Subgroup.normal_le_normalCore
#check Subgroup.normalCore_eq_ker
-- 4.11, 4.12: decomposition into orbits and the class equation.
#check MulAction.selfEquivSigmaOrbits
#check Group.sum_card_conj_classes_eq_card
#check Group.nat_card_center_add_sum_card_noncenter_eq_card
-- 4.13: Cauchy's theorem.
#check exists_prime_orderOf_dvd_card'
-- 4.14: elementwise and cardinality definitions of p-groups.
#check IsPGroup.iff_card
-- 4.15: GAP: classification of groups of order 2p as cyclic or dihedral.
-- The missing result assumes p is an odd prime and proves every group of order
-- 2p is either C_{2p} or the nonabelian semidirect product C_p ⋊ C₂, up to
-- isomorphism; the existing APIs only provide ingredients for that proof.
-- RELATED: Cauchy, index-two normality, and SemidirectProduct.mulEquivSubgroup.
-- 4.16: the centre of a nontrivial finite p-group is nontrivial.
#check IsPGroup.card_center_eq_prime_pow
-- 4.17: RELATED: p-power subgroups exist; GAP for normal subgroups of every p-power order.
#check Sylow.exists_subgroup_card_pow_prime
-- The missing strengthening asks for a normal subgroup of each order p^k in a
-- finite p-group (with a compatible chain), rather than merely some subgroup
-- of that order supplied by Sylow theory.
-- 4.18: groups of order p² are abelian; decomposition uses Chapter 1.
#check IsPGroup.isMulCommutative_of_card_eq_prime_sq
-- 4.19: a cyclic quotient by a central subgroup forces commutativity.
#check commutative_of_cyclic_center_quotient
-- 4.20: RELATED: proof by commuting coset representatives; no dedicated statement located.
-- 4.21: GAP: the complete order-eight classification (D4 or Q8 in the nonabelian case).
-- Missing is the order-eight enumeration proving that the only nonabelian
-- isomorphism types are D₄ and Q₈, while the three abelian cases are C₈,
-- C₄ × C₂, and C₂ × C₂ × C₂; the constructors above do not establish exhaustiveness.
-- 4.22: RELATED: core-free coset actions give smaller faithful permutation representations.
#check Subgroup.normalCore_eq_ker
#check MonoidHom.ker_eq_bot_iff
-- 4.23: GAP: the explicit order-six classification; see 4.15.
-- The absent statement gives the complete list C₆ and S₃ (equivalently D₃),
-- with an isomorphism proof from the normal subgroup of order 3 and the possible
-- conjugation actions of the quotient of order 2.
-- 4.24, 4.25: sign, parity and its uniqueness.
#check Equiv.Perm.signAux
#check Equiv.Perm.sign_swap
#check Equiv.Perm.eq_sign_of_surjective_hom
-- 4.26: disjoint cycle decomposition.
#check Equiv.Perm.cycleFactorsFinset
#check Equiv.Perm.cycleType
-- 4.27: transposition decomposition and parity.
#check Equiv.Perm.swapFactors
#check Equiv.Perm.sign_prod_list_swap
-- 4.28: alternating groups are generated by 3-cycles.
#check alternatingGroup.closure_isThreeCycles_eq_top
-- 4.29, 4.30, 4.31: conjugating cycles, cycle types and conjugacy classes.
#check Equiv.Perm.cycleType_conj
#check Equiv.Perm.isConj_iff_cycleType_eq
#check Equiv.Perm.partition_eq_of_isConj
-- 4.32: RELATED: cycle-type API; GAP for all displayed A4/A5 class counts and tables.
-- Missing are the concrete conjugacy-class enumerations for A₄ and A₅: class
-- representatives, class sizes, splitting of S_n classes, and the resulting
-- conjugacy tables used in Milne's displayed calculations.
-- 4.33: simplicity of A_n for n ≥ 5.
#check alternatingGroup.normal_subgroup_eq_bot_or_eq_top
-- 4.34: RELATED: the Klein four subgroup of A4; A2/A3 follow by specialization.
#check alternatingGroup.kleinFour
-- 4.35: the normal closure of a 3-cycle is A_n.
#check Equiv.Perm.IsThreeCycle.alternating_normalClosure
-- 4.36: RELATED: simplicity above implies a nontrivial normal subgroup contains 3-cycles;
-- GAP for Milne's particular support-reduction proof as a standalone lemma.
-- The absent lemma is the explicit support-reduction argument: choose a
-- nonidentity element of a normal subgroup, conjugate it to reduce its support,
-- and conclude that a 3-cycle lies in the subgroup.
-- 4.37: RELATED: a nontrivial normal subgroup of S_n contains A_n.
#check Equiv.Perm.alternatingGroup_le_of_normal
-- 4.38: GAP: complete description of conjugacy-class splitting in A_n.
-- The absent theorem gives the exact criterion for an Sₙ conjugacy class to
-- split in Aₙ (distinct odd cycle lengths), and computes the two resulting
-- Aₙ classes and their centralizers when it does split.
-- 4.39: nonsolvability of symmetric groups of degree at least five.
#check Equiv.Perm.not_solvable
-- Todd-Coxeter (pp. 70-71): GAP: coset tables, deductions and the worked presentation.
-- This repeats the algorithmic gap in the action chapter: no checked coset
-- table, deduction procedure, or verification of the worked finite-index
-- computation is exposed alongside the abstract coset-action theorems.
-- Primitive actions and blocks: Mathlib's IsPreprimitive includes transitivity,
-- unlike the PDF's preliminary convention allowing trivial actions.
#check MulAction.IsBlock
#check MulAction.IsPreprimitive
-- 4.40: GAP: the explicit block systems for C4,D4,A4,S4.
-- What is missing is a worked list of all blocks and block systems for these
-- actions, followed by the primitive/imprimitive classification; `IsBlock`
-- supplies the predicate but not those finite case calculations.
-- 4.41: double transitivity implies primitivity.
#check MulAction.isPreprimitive_of_is_two_pretransitive
-- 4.42: transitivity is part of IsPreprimitive; see the convention note above.
-- 4.43, 4.44: RELATED: blocks and their set stabilizers; strict inclusions need specialization.
#check MulAction.IsBlock
-- 4.45: primitivity is maximality of a point stabilizer (in a nontrivial transitive action).
#check MulAction.isCoatom_stabilizer_iff_preprimitive

-- Chapter 5. The Sylow theorems; applications.

-- 5.1: fixed-point congruence for a finite p-group action.
#check IsPGroup.card_modEq_card_fixedPoints
-- 5.2: Sylow I, including subgroups of all dividing p-power orders.
#check Sylow
#check Sylow.exists_subgroup_card_pow_prime
#check Sylow.card_eq_multiplicity
-- 5.3: RELATED: cardinality of GL_n(F_q); GAP for the full upper-unitriangular Sylow example.
-- The missing result identifies a Sylow p-subgroup of GL(n,q) concretely as the
-- unitriangular matrices (when p is the characteristic of the finite field),
-- including its order and the flag it stabilizes.
#check Matrix.card_GL_field
-- 5.4, 5.5: Cauchy and intermediate p-powers are already covered by 4.13 and 5.2.
-- 5.6: conjugacy, congruence, divisibility and containment in Sylow subgroups.
#check Sylow.isPretransitive_of_finite
#check card_sylow_modEq_one
#check Sylow.card_dvd_index
#check IsPGroup.exists_le_sylow
-- 5.7: a p-subgroup normalizing a Sylow p-subgroup is contained in it.
#check IsPGroup.inf_normalizer_sylow
-- 5.8: normal Sylow subgroups are unique and characteristic.
#check Sylow.unique_of_normal
#check Sylow.normal_of_subsingleton
#check Sylow.characteristic_of_normal
-- 5.9: normal Sylow subgroups give a direct product.
#check Sylow.directProductOfNormal
-- 5.10: GAP: Sylow subgroups of GL(V) described via maximal flags.
-- What is missing is the construction from a complete flag: its unipotent
-- stabilizer is a p-subgroup, has the Sylow cardinality, and every Sylow is
-- conjugate to one obtained this way.
-- 5.11: GAP: tetrahedral geometric description of Sylow subgroups of S4.
-- The API does not package the geometric realization of S4 as tetrahedron
-- symmetries, nor identify the resulting Sylow-2 subgroup with its chosen
-- four-vertex permutations (abstract Sylow facts remain available above).
-- 5.12: a subgroup's Sylow subgroup comes from an ambient Sylow subgroup.
#check Sylow.exists_comap_subtype_eq
-- RELATED: conjugacy in 5.6 changes this ambient Sylow to the prescribed P.
-- 5.13: GAP: the order-99 classification as C99 or C3 × C33.
-- Missing is the finite case analysis that forces an abelian group and then
-- applies the abelian classification to produce exactly these two types.
-- 5.14: GAP: complete classification and uniqueness for order pq, p < q.
-- Missing are the existence conditions for the nonabelian semidirect product,
-- the count of isomorphism types, and the proof that no other action occurs.
-- 5.15: GAP: classification of order-30 groups and their normal subgroup of order 15.
-- Missing is the complete Sylow-action case split yielding a characteristic
-- or normal subgroup of order 15 and the resulting list of order-30 groups.
-- 5.16: GAP: the five isomorphism classes of groups of order 12.
-- The available Sylow and action lemmas do not assemble the five presentations
-- or prove pairwise nonisomorphism (C12, C2 × C6, C2 × S3, A4, and C4 ⋊ C3).
-- 5.17: GAP: the five isomorphism classes of groups of order p³ (p odd).
-- Missing are the classification of the abelian cases and the two nonabelian
-- presentations, together with the argument that these five cases are complete.
-- 5.18: GAP: nonsimplicity of orders 2p^n, 4p^n and 8p^n (p odd).
-- Missing is the uniform construction of a proper nontrivial normal subgroup
-- in each order family, including the separate 2-, 4-, and 8-divisibility cases.
-- 5.19: GAP: every simple group of order 60 is isomorphic to A5.
-- Missing is the order-60 Sylow counting/action argument proving simplicity
-- forces the alternating-group action and hence an isomorphism with A5.
-- RELATED for 5.13-5.19: the Sylow counting, complements and action APIs above.

-- Chapter 6. Subnormal series; solvable and nilpotent groups.

-- Subnormal/normal/composition series (pp. 87-89).
-- RELATED: general relation series and Jordan-Holder lattices.
#check RelSeries
#check CompositionSeries
#check JordanHolderLattice
-- 6.1: GAP: the explicit composition series of S3, S4 and cyclic groups in the examples.
-- The series datatype exists, but no compact entries here construct the listed
-- normal chains, verify simple factors, and print their factor isomorphism types.
-- 6.2, 6.3(a): abstract Jordan-Holder uniqueness, without finiteness of the underlying object.
-- The missing bridge is the group-specific subnormal-series instance: from a
-- finite group one still needs existence of a composition series and a theorem
-- comparing its simple factors up to permutation and group isomorphism.
#check CompositionSeries.jordan_holder
#check CompositionSeries.Equivalent.length_eq
-- GAP: a JordanHolderLattice instance for arbitrary group subnormal series was not located;
-- the theorem above must not be mistaken for the group-specific theorem without that bridge.
-- 6.3(b): GAP: the Dedekind-domain projective-module counterexample to uniqueness.
-- Missing is the explicit nonprincipal ideal pair 𝔞, 𝔟 with 𝔞𝔟 principal:
-- the projective module 𝔞 ⊕ 𝔟 is isomorphic to R², while its rank-one projective
-- summands give distinct decomposition data {𝔞,𝔟} and {R,R} in this broader category.
-- Solvability and 6.4: GAP: Feit-Thompson (odd-order theorem) is not in this Mathlib.
-- In particular, there is no theorem here turning finiteness plus odd group
-- order into `IsSolvable`, nor the proof of the theorem's group-theoretic input.
#check IsSolvable
-- 6.5: GAP: the displayed upper-triangular GL2 group and its solvability calculation.
-- Missing is the concrete subgroup definition, its derived subgroup computation,
-- and the conclusion that the derived series reaches 1 in the stated number of steps.
-- 6.6: solvability passes to subgroups, quotients and extensions.
#check subgroup_solvable_of_solvable
#check solvable_quotient_of_solvable
#check solvable_of_ker_le_range
-- 6.7: finite p-groups are nilpotent, hence solvable.
#check IsPGroup.isNilpotent
#check IsNilpotent.to_isSolvable
-- Commutators, the derived subgroup and derived series.
#check commutatorElement
#check commutator
#check derivedSeries
-- 6.8: GAP: solvability of the stabilizer of a maximal flag.
-- Missing is the matrix-group argument that a complete-flag stabilizer is
-- triangular, with abelian diagonal quotient and nilpotent unipotent kernel.
-- 6.9: the commutator subgroup is characteristic; abelianization is universal.
#check Subgroup.commutator_characteristic
#check Abelianization
#check Abelianization.lift
-- 6.10: the derived series terminates precisely for solvable groups (Mathlib's definition).
#check IsSolvable.solvable
#check derivedSeries_characteristic
-- GAP: minimality among all solvable series / solvable length not identified as one API.
-- Existing derived-series termination does not expose the least possible length
-- over all subnormal series, nor the theorem equating that minimum with derived length.
-- 6.11: GAP: minimal order 96 for non-single commutators and the Ore conjecture.
-- Missing are both the finite enumeration assertion (the first group having an
-- element of its derived subgroup that is not itself a single commutator has
-- order 96), and Ore's theorem: every element of a finite nonabelian simple
-- group is a single commutator.

-- Nilpotent groups, upper/lower central series and nilpotency class.
#check Group.IsNilpotent
#check Subgroup.upperCentralSeries
#check Subgroup.lowerCentralSeries
#check Group.nilpotencyClass
-- 6.12: nilpotent implies solvable; GAP for the displayed triangular counterexample.
-- The missing example is the invertible upper-triangular 2 × 2 matrix group B:
-- over a field with more than two elements, B is solvable, while B/Z(B) is
-- nontrivial with trivial centre and is therefore nonnilpotent.
#check IsNilpotent.to_isSolvable
-- 6.13: subgroups and quotients of nilpotent groups.
#check Subgroup.isNilpotent
#check Group.nilpotent_quotient_of_nilpotent
-- 6.14: GAP: the explicit example where a subgroup's centre grows beyond the ambient centre.
-- Missing is the displayed example U≤B: upper-unitriangular 2×2 matrices U
-- are abelian, but intersect the scalar centre of the upper-triangular group B
-- trivially (over a field with more than two elements). Centres of subgroups
-- need not be obtained by intersecting with the ambient centre.
-- 6.15: termination of the lower central series characterizes nilpotency.
#check Subgroup.isNilpotent_iff_lowerCentralSeries
#check Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
-- RELATED: the iterated element-commutator formulation follows from the series generators.
-- 6.16: a central kernel raises nilpotency class by at most one.
#check Subgroup.isNilpotent_of_ker_le_center
#check Group.nilpotencyClass_le_of_ker_le_center
-- 6.17: finite p-groups are nilpotent.
#check IsPGroup.isNilpotent
-- 6.18: finite nilpotent groups are products of Sylow subgroups.
#check Group.isNilpotent_of_finite_tfae
#check Sylow.directProductOfNormal
-- 6.19: Sylow normalizers are self-normalizing.
#check Sylow.normalizer_normalizer
-- RELATED: this is the H = N_G(P) case; GAP for the stated arbitrary overgroup H.
-- The missing statement starts with P Sylow in finite G and N_G(P) ≤ H ≤ G,
-- then proves N_G(H) = H; the available theorem only displays the special
-- self-normalizing conclusion when H itself is N_G(P).
-- 6.20: proper subgroups of a nilpotent group are strictly smaller than their normalizers.
#check NormalizerCondition
#check normalizerCondition_of_isNilpotent
-- 6.21: specialize the Sylow product decomposition to abelian groups.
-- 6.22: Frattini's argument.
#check Sylow.normalizer_sup_eq_top
-- 6.23: finite nilpotency iff all maximal subgroups are normal (one clause of TFAE).
#check Group.isNilpotent_of_finite_tfae
-- 6.24: GAP: commutator maps of class-at-most-two central extensions.
-- For A central in G and B=G/A abelian, missing is the induced map ∧²B → A,
-- whose image is [G,G] and whose values on b∧b′ are the individual commutators.
-- Also missing is realization of every such alternating map by an extension.
-- This map alone does not classify extensions: symmetric extension data can differ.
-- Caution (p. 93): 'metabelian' usually means abelian derived subgroup, not class exactly 2.

-- Groups with operators: actions by automorphisms and equivariant homomorphisms.
#check MulDistribMulAction
#check MulDistribMulActionHom
-- 6.25: trivial operators, conjugation, and modules as abelian groups with operators.
#check ConjAct
#check Module
-- 6.26, 6.27, 6.28: RELATED: underlying isomorphism/correspondence theorems are in Chapter 1.
-- GAP: full bundled operator-equivariant group versions not located.
-- The missing layer would make normal/subnormal subgroups and quotient maps
-- carry the operator action, with equivariant versions of the Chapter 1 theorems.
-- 6.29: GAP: operator composition series (chief series and characteristic series).
-- Missing are existence and refinement theorems for minimal operator-invariant
-- normal subgroups, plus the characteristic-series construction in the finite case.
-- 6.30: GAP: directly indecomposable groups and the S3 / cyclic prime-power examples.
-- Missing is an API for a nontrivial direct-product decomposition, its
-- indecomposability predicate, and the proofs for the examples listed by Milne.
-- 6.31: GAP: group Krull-Schmidt theorem, including the exchange property.
-- Missing is the finite direct-product uniqueness theorem: two decompositions
-- into directly indecomposable groups have matching factors up to permutation/isomorphism.
-- 6.32: RELATED: vector-space bases give the two decompositions of F_p²; p must be odd.
#check Module.Basis
-- 6.33: GAP: Krull-Schmidt with chain conditions / operators and its uniqueness corollary.
-- Missing are the ascending/descending chain hypotheses on normal subgroups with
-- operators, the exchange argument, and the resulting uniqueness statement.

-- Chapter 7. Representations of finite groups.

-- Algebras, opposite algebras, simple and semisimple modules (p. 101).
#check Algebra
#check MulOpposite
#check IsSimpleModule
#check IsSemisimpleModule
-- Matrix / linear representations; group elements act by invertible linear maps.
#check Representation
#check Representation.asGroupHom
-- 7.1(a): GAP: the particular faithful Q8 -> GL2(C) representation.
-- Missing is the explicit assignment of quaternion generators to complex 2-by-2
-- matrices, verification of the relations, and proof that the kernel is trivial.
-- 7.1(b): permutation and regular representations.
#check Representation.ofMulAction
#check Representation.leftRegular
-- 7.1(c): RELATED: roots of unity give cyclic characters; GAP for the displayed modular matrix example.
-- Missing is the concrete representation over the indicated modular field and
-- the calculation of its eigenvalues/character; roots-of-unity APIs only give ingredients.
#check IsPrimitiveRoot
-- 7.2: GAP: Burnside's finite-exponent theorem for finitely generated linear groups.
-- Missing is the theorem that a finitely generated subgroup of GL_n(C) with
-- bounded element orders is finite, including the dependence on n and the exponent.
-- Roots of unity (p. 102).
#check rootsOfUnity
#check HasEnoughRootsOfUnity
#check IsPrimitiveRoot.card_rootsOfUnity
-- 7.3: RELATED: eigenspaces and simultaneous diagonalization for abelian representations.
#check Module.End.eigenspace
#check Module.End.HasEigenvector
-- GAP: the precise cyclic and finite-abelian character decompositions in this example.
-- Missing are the statements that every irreducible representation of a finite
-- abelian group is one-dimensional and that all characters arise from the listed
-- roots of unity, with the explicit decomposition into character eigenspaces.
-- Subrepresentations, quotient representations, irreducibility and semisimplicity.
#check Representation.subrepresentation
#check Representation.quotient
#check Representation.IsIrreducible
#check Representation.IsSemisimpleRepresentation
-- 7.4: Maschke: every invariant subspace has an invariant complement.
#check MonoidAlgebra.Submodule.exists_isCompl
-- 7.5, 7.6, 7.7: RELATED: orthogonal complements and averaging projections.
#check LinearMap.BilinForm.orthogonal
#check LinearMap.equivariantProjection
-- GAP: Milne's invariant averaged bilinear form and positivity lemmas in this exact formulation.
-- The available averaging maps do not package the form, its invariance, and its
-- positive-definiteness/nondegeneracy as one construction with these hypotheses.
-- 7.8: GAP: the stated unitarizability theorems for real, complex and compact-group representations.
-- Missing are the change-of-basis theorem making a finite-group representation
-- unitary/orthogonal and the separate compact-group result using Haar integration.
-- Group algebra and its modules (pp. 105-106).
#check MonoidAlgebra
#check Representation.asAlgebraHom
#check Representation.asModule
#check Representation.ofModule
-- 7.9: semisimplicity of group-algebra modules (Maschke), then decomposition into simples.
variable (k G V : Type*) [Field k] [Group G] [Finite G]
    [NeZero (Nat.card G : k)] [AddCommGroup V] [Module (MonoidAlgebra k G) V] in
#synth IsSemisimpleModule (MonoidAlgebra k G) V
#check IsSemisimpleModule.exists_linearEquiv_dfinsupp
-- 7.10, 7.11: Jordan-Holder for modules; finite-length hypotheses matter.
#check JordanHolderModule.instJordanHolderLattice
#check CompositionSeries.jordan_holder
-- RELATED: the abstract uniqueness theorem; GAP for the displayed existence-and-filtration package.
-- Missing is a turnkey construction of a finite composition series for each
-- module, its simple factors, and the filtration-independent multiplicity theorem.
-- 7.12, 7.13: sums of simples, direct-sum decompositions, complemented submodules.
#check IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top
#check sSup_simples_eq_top_iff_isSemisimpleModule
#check isSemisimpleModule_iff_exists_linearEquiv_dfinsupp
-- 7.14: submodules, quotients and sums remain semisimple.
#check IsSemisimpleModule.submodule
#check IsSemisimpleModule.quotient
#check isSemisimpleModule_of_isSemisimpleModule_submodule
-- Isotypic components; 7.15: fully invariant submodules are sums of components.
#check isotypicComponent
#check isotypicComponents
#check Submodule.IsFullyInvariant
#check isFullyInvariant_iff_sSup_isotypicComponents
-- 7.16: RELATED: endomorphisms of the regular module are right multiplications.
#check Module.End
#check LinearMap.mulRight
-- Simple / semisimple algebras; 7.17: isotypic components and two-sided ideals.
#check IsSimpleRing
#check IsSemisimpleRing
#check isFullyInvariant_iff_isTwoSided
#check mem_isotypicComponents_iff
-- 7.18: division algebras, their regular simple module and centre.
#check DivisionRing
#check Subring.center
-- 7.19: RELATED: matrix rings over division rings are simple and Artinian.
#check Matrix
#check IsSimpleRing.exists_ringEquiv_matrix_divisionRing
-- GAP: the complete worked matrix-unit calculation / description of left ideals as one API.
-- Missing is the worked matrix-unit argument that the subspaces L(i), consisting
-- of matrices supported in one fixed column, are minimal left ideals and that
-- M_n(D) is their direct sum; this is separate from the two-sided simplicity API.
-- 7.20: quaternion algebras; the middle Mathlib parameter is zero for Milne's convention.
variable (F : Type*) [Field F] (a b : F) in
#check QuaternionAlgebra F a 0 b
-- GAP: the division-or-M2 dichotomy in this example (requiring characteristic ≠ 2).
-- Missing is the case split for QuaternionAlgebra F a 0 b: either it has no
-- nonzero zero divisors and is a division algebra, or it is explicitly isomorphic
-- to M₂(F), under the characteristic and parameter assumptions in the text.
-- 7.21: centralizers of scalar matrices / all matrices; RELATED API.
#check Subalgebra.centralizer
-- 7.22, 7.23: double centralizer / density theorem for semisimple modules.
-- RELATED: the displayed density and finite-module APIs are the ingredients for
-- the exact double-centralizer equality and simultaneous interpolation statement.
#check jacobson_density
#check Module.Finite.toModuleEnd_moduleEnd_surjective
-- 7.24: Schur's lemma.
#check LinearMap.bijective_or_eq_zero
#check Module.End.instDivisionRing
-- 7.25: Wedderburn-Artin; finite-dimensional simple algebras are matrix algebras.
#check IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite
-- 7.26, 7.27: simple Artinian rings are semisimple and isotypic.
#check IsSimpleRing.isSemisimpleRing_iff_isArtinianRing
#check IsSimpleRing.isIsotypic
-- 7.28, 7.29: simple modules are minimal ideals; all modules are sums of one simple type.
#check IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
#check IsIsotypicOfType.linearEquiv_finsupp
-- RELATED: GAP for the exact same-F-dimension equivalence in 7.29 as one theorem.
-- In the chapter's finite-dimensional setting, missing is the packaged corollary
-- for a simple F-algebra A: every A-module is a direct sum of copies of one
-- simple module S, and two A-modules of equal F-dimension are isomorphic.
-- 7.30: GAP: uniqueness of the division ring and matrix size in Wedderburn-Artin.
-- The existence equivalence does not expose uniqueness of the division ring up to
-- isomorphism and uniqueness of the matrix size (or the appropriate opposite ring).
-- 7.31: over an algebraically closed field, finite-dimensional simple algebras split.
#check IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
-- RELATED: specialize to a division algebra to obtain the stated result.
-- 7.32: finite division rings are fields; Brauer equivalence and the quotient set.
#check littleWedderburn
#check BrauerGroup
-- GAP: the Brauer group law / field-specific classifications are not supplied by this quotient.
-- `BrauerGroup` provides the ambient quotient data, but the missing API gives its
-- tensor-product group law and identifies concrete classes over specified fields.
-- Caution: the real division-algebra assertion needs centrality to exclude C.
-- 7.33: finite products of semisimple rings are semisimple (typeclass instances).
-- 7.34, 7.35: endomorphism algebras decompose along isotypic components.
#check IsSemisimpleModule.endAlgEquiv
#check IsSemisimpleModule.exists_end_algEquiv_pi_matrix_divisionRing
-- 7.36: semisimple algebras are products of simple matrix algebras.
#check IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite
-- 7.37: RELATED: isotypic decomposition and matrix-product description above;
-- GAP for the whole numbered package of simple-module classification and multiplicities.
-- Missing is the exact product-algebra statement: for A = A₁ × ⋯ × Aₜ, the
-- chosen simple Aᵢ-modules are exactly the simple A-modules, every finite-
-- dimensional A-module is ⨁ rᵢSᵢ, and the multiplicities rᵢ are unique.
-- 7.38: GAP: dim Z(F[G]) = number of conjugacy classes, as a standalone theorem.
-- Missing is the explicit basis of the group-algebra centre by conjugacy-class
-- sums and the resulting equality of its dimension and the class count.
-- 7.39: finitely supported functions on a finite group are all functions.
#check Finsupp.linearEquivFunOnFinite
-- RELATED: conjugacy-invariance describes the centre of the group algebra.
-- 7.40: split semisimple group algebras; combine Maschke with this algebra theorem.
#check IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
-- 7.41: GAP: the full irreducible-count, regular-multiplicity, and sum-of-squares package.
-- For finite G over an algebraically closed field of characteristic zero,
-- missing is the combined statement: the number of irreducibles equals the
-- number of conjugacy classes, each S occurs in the regular representation
-- with multiplicity dim S, and ∑ (dim S)² = |G|.
-- Characters: trace, value at the identity, invariance under isomorphism and conjugacy.
#check Representation.character
#check Representation.char_one
#check Representation.char_iso
#check Representation.char_conj
-- 7.42: RELATED: trace is additive under direct sums; GAP for a named character-sum API.
-- Missing is the explicit class-function sum formula expressing the regular and
-- direct-sum characters as sums of irreducible character values.
#check LinearMap.trace_prodMap
-- 7.43: RELATED: orthonormality below implies independence of inequivalent simple characters.
-- 7.44: GAP: equality of characters iff isomorphism, for arbitrary finite-dimensional char-zero reps.
-- Missing is the converse direction: equal traces on every group element imply an
-- intertwining isomorphism, with the finite-dimensional characteristic-zero assumptions.
-- 7.45: GAP: modular-character counterexamples and the divisible multiplicity caveat.
-- In characteristic p, the nontrivial C_p action by matrices [[1,i],[0,1]]
-- has the same trace as the trivial two-dimensional representation. Also p copies
-- of any representation have zero character, even if p does not divide |G|.
-- Missing are these examples and Brauer–Nesbitt's replacement: semisimple
-- representations with equal characteristic polynomials on the algebra are isomorphic.
-- 7.46: GAP: virtual characters and their integral basis of irreducible characters.
-- Missing is the Grothendieck/group-completion construction of virtual characters
-- and the theorem that irreducibles form an integral basis there.
-- 7.47: GAP: irreducible characters form a basis of class functions.
-- Over an algebraically closed field of characteristic zero, missing is a basis
-- of the space of conjugacy-invariant functions indexed by irreducible modules.
-- This must prove both linear independence and spanning; an individual character
-- being conjugacy invariant does not prove the basis theorem.
-- 7.48: RELATED: the finite-sum pairing is realized by the character identities below;
-- The PDF assumes a conjugation-stable subfield of C and uses the Hermitian
-- pairing (1/|G|)∑ f₁(g)·conj(f₂(g)); on characters, conj(χ(g))=χ(g⁻¹).
-- The algebraic character APIs below express the corresponding inverse-element sums.
-- 7.49: averaging is projection onto invariants.
#check GroupAlgebra.average
#check Representation.invariants
#check Representation.averageMap
#check Representation.isProj_averageMap
-- 7.50: average character equals dimension of invariants.
#check Representation.card_inv_mul_sum_char_eq_finrank
-- 7.51: character pairing computes dimension of intertwining maps.
#check Representation.IntertwiningMap
#check Representation.card_inv_mul_sum_char_mul_char_eq_finrank
-- 7.52: Schur orthogonality.
#check Representation.char_orthonormal
-- The ensuing character criterion for irreducibility.
#check FDRep.simple_iff_char_is_norm_one
-- 7.53, 7.54, 7.55, 7.56: GAP: explicit character tables of C3, S3, D4 and Q8.
-- Missing are the named irreducible representations, conjugacy-class ordering,
-- character values, and orthogonality checks for each of the four tables.
-- The table entries can be represented using Representation.character above.
-- GAP: the final discussion of recovering normal subgroups / commutator from character kernels.
-- For complex characters, recover ker(ρ) from χ(g)=χ(1). Missing is the
-- statement that each normal N is the intersection of kernels of the irreducibles
-- factoring through G/N, and that [G,G] is the intersection of kernels of all
-- one-dimensional characters. These make the normal subgroups readable from the table.

-- Chapter exercises. These also index the corresponding solutions in Appendix B.
-- RELATED entries name tools for the exercise, rather than claim a complete worked solution.

-- 1-1: RELATED: unique Q8 involution, normal subgroups, and comparison with D4.
#check QuaternionGroup.orderOf_a
#check QuaternionGroup.orderOf_xa
-- GAP: the combined classification/counterexample statement.
-- The missing part is the proof that the unique involution is central and that
-- every subgroup of Q8 is normal, followed by the nonisomorphism Q8 ≄ D4.
-- 1-2: GAP: two finite-order integral matrices with infinite-order product.
-- What is missing is this concrete GL₂(ℤ) calculation: a⁴ = 1, b³ = 1,
-- while ab has infinite order, giving a finitely generated infinite subgroup.
-- 1-3: even-order groups have an involution (Cauchy at p = 2).
#check exists_prime_orderOf_dvd_card'
-- 1-4: RELATED: factorial divisibility from the Young subgroup of a symmetric group.
#check Fintype.card_perm
#check Subgroup.card_subgroup_dvd_card
-- 1-5: RELATED: powers lie in a normal subgroup of the corresponding index.
#check pow_card_eq_one'
#check QuotientGroup.eq_one_iff
-- GAP: the nonnormal counterexample is not packaged here.
-- The missing witness is a finite-index-n subgroup H that is not normal and an
-- element g with gⁿ ∉ H; the quotient argument above only handles normal H.
-- 1-6(a): exponent-two commutativity.
#check Monoid.exponent
#check mul_comm_of_exponent_two
-- 1-6(b): GAP: the nonabelian exponent-p upper-unitriangular matrix example.
-- The requested example is the nonabelian group of 3×3 upper-unitriangular
-- matrices over 𝔽_p (p odd), whose elements have exponent p; no bundled example
-- connects that concrete matrix group to the exponent-two commutativity lemma.
-- 1-7: commensurability is an equivalence relation.
#check Subgroup.Commensurable
#check Subgroup.Commensurable.equivalence
-- 1-8, 1-9: RELATED: constructing groups from finite cancellation / one-sided division.
#check Group.ofLeftAxioms
-- GAP: the exact weaker hypotheses and the counterexample in 1-9 as a single API.
-- Exercise 1-8 asks for the finite, associative, nonempty, two-sided cancellation
-- argument. Exercise 1-9 weakens this to bijective left translations and one
-- injective right translation; the missing counterexample is the right-projection
-- law x*y = y on a set with at least two elements.
-- 1-10: group completion of a cancellative commutative monoid.
#check Algebra.GrothendieckGroup
#check Algebra.GrothendieckGroup.of_injective
-- The converse is cancellation inherited by a submonoid of a group.

-- 2-1: GAP: D_(2n) ≃ C2 × D_n for odd n.
-- The missing construction identifies ⟨aⁿ⟩ with C₂, ⟨a²,b⟩ with D_n, proves
-- both factors commute and intersect trivially, and packages the resulting
-- internal direct-product equivalence.
-- 2-2: free abelian group and its universal property.
#check FreeAbelianGroup
#check FreeAbelianGroup.lift
-- RELATED: identify the commuting-generator presentation using universal properties.
-- 2-3: GAP: unique roots, commuting powers and absence of nontrivial divisible elements in free groups.
-- Specifically absent are: aⁿ = bⁿ (n > 1) ⇒ a = b; commuting nonzero powers
-- ⇒ commuting elements; and the conclusion that an element having roots of every
-- positive degree is trivial, all as theorems for arbitrary free groups.
-- 2-4: RELATED: embeddings and surjections induced by maps of free generators.
#check FreeGroup.map_injective
#check FreeGroup.map_surjective
-- GAP: the nonfreeness of Z² and trivial centre of a free group of rank > 1.
-- The existing map APIs cover universal maps, but no packaged invariant proves
-- that F₁ × F₁ is not free or that the centre of F_n is trivial for n > 1.
-- 2-5: GAP: unique order-two subgroup and dihedral central quotient of generalized quaternion groups.
-- Missing are the generalized statement for Q_n: its unique subgroup of order 2
-- equals its centre, and Q_n/Z(Q_n) is the corresponding dihedral group.
-- 2-6: RELATED: finite/infinite dihedral groups; exact presentation identifications need proofs.
#check DihedralGroup 0
-- 2-7: GAP: triviality of the specified three-generator presentation.
-- The exercise asks for a presentation-level reduction showing that the relations
-- force x = y = z = 1; PresentedGroup supplies the object but not this computation.
-- 2-8: RELATED: index-two free subgroup and its Schreier basis.
#check subgroupIsFreeOfIsFree
-- GAP: the particular minimal generating set of the kernel F2 -> C2.
-- Schreier freeness is available, but the explicit exercise output is missing:
-- identify the kernel of F₂ → C₂, exhibit the three generators x², xy, y²,
-- and prove that this rank-three free basis is minimal.
-- 2-9: GAP: the specified word in BS(3,5) vanishes in every finite quotient.
-- This is the concrete non-residual-finiteness witness for the Baumslag–Solitar
-- presentation BS(3,5): the designated nontrivial word maps to 1 in every finite
-- quotient, with no corresponding finite-quotient argument located here.

-- 3-1: GAP: Q8 has no nontrivial semidirect product decomposition.
-- Missing is the case analysis ruling out Q8 ≅ N ⋊ H whenever both factors are
-- nontrivial, using its unique subgroup of order two and subgroup lattice.
-- 3-2: RELATED: unique coprime-order subgroups give normal complements (1.51).
#check Subgroup.IsComplement'
-- 3-3, 3-4: GAP: GL2(F2) ≃ S3 and Aut(Q8) ≃ S4.
-- The absent pieces are the explicit permutation identifications: GL₂(𝔽₂) acts
-- faithfully on its three nonzero vectors. For Aut(Q8) the missing work is an
-- explicit enumeration of the 24 automorphisms and a concrete identification
-- of their multiplication with S₄; Q8 has only three cyclic subgroups of order 4.
-- 3-5: GAP: the displayed real matrix group is R² ⋊ (Rˣ × Rˣ), not their direct product.
-- Missing is the concrete factorization of the upper-triangular matrices and the
-- conjugation action of (a,d) on R², plus a witness that the two factors do not
-- commute and therefore the product is not direct.
-- 3-6: RELATED: automorphisms of Z; GAP: the explicit Aut(S3) identification.
-- The missing finite calculation is that every automorphism of S₃ is inner,
-- yielding Aut(S₃) ≃ S₃; the cyclic-group API only covers Aut(ℤ) ≃ C₂ here.
#check IsCyclic.mulAutMulEquiv
-- 3-7(a,b): element orders under projection and in a direct product.
#check orderOf_map_dvd
#check Prod.orderOf
-- GAP: the full kernel-divisor formula, S5 calculation, wreath-product and inversion-action examples.
-- Missing are the uniform formula o(nq)=k·o(q) with k | |N|, the commuting-case
-- lcm formula, and the worked S₅ and cyclic-permutation examples, including the
-- element of order p² in (C_p)^p ⋊ C_p.
-- 3-8: GAP: the general centre formula for N ⋊ Q and its two abelian specializations.
-- The absent theorem describes central pairs (n,q) in a semidirect product and
-- specializes it to abelian N and Q; no single centre-of-SemidirectProduct API
-- packages these equations.
-- 3-9: GAP: the nonabelian snake lemma with normal vertical homomorphisms.
-- Missing is the diagram theorem relating kernels and cokernels when the vertical
-- maps are normal homomorphisms, together with the induced connecting map; the
-- usual additive/abelian snake lemma does not cover this group statement.
-- 3-10: the multiplication map from an internal semidirect product.
#check SemidirectProduct.monoidHomSubgroup
-- 3-11: retractions and split extensions.
#check GroupExtension.Splitting.semidirectProductMulEquiv
#check SemidirectProduct.rightHom_comp_inr

-- 4-1: RELATED: maps of transitive G-sets from the quotient universal construction.
#check MulAction.ofQuotientStabilizer
-- GAP: the full transporter/coset bijection for G-maps.
-- The missing result parametrizes G-equivariant maps G/H₁ → G/H₂ by cosets
-- gH₂ satisfying H₁ ≤ gH₂g⁻¹, including the natural one-to-one correspondence.
-- 4-2, 4-3: GAP: proper finite-index subgroups do not meet every conjugacy class;
-- hence conjugacy-class representatives generate, with an infinite-index counterexample.
-- Missing are the finite and finite-index covering arguments, the infinite-group
-- counterexample, and the deduction that any choice of finite conjugacy-class
-- representatives generates the whole group.
-- 4-4: GAP: classification of nonabelian order-p³ groups; see 5.17.
-- The absent conclusion is the classification for odd p: every noncommutative
-- group of order p³ is one of the two explicit constructions from 3.14/3.15.
-- 4-5: a subgroup of index the smallest prime divisor of |G| is normal.
#check Subgroup.normal_of_index_eq_minFac_card
-- 4-6: GAP: a group of twice odd order has a subgroup of index two.
-- Missing is the Cayley-theorem argument that the action on 2m letters yields a
-- homomorphism onto C₂, hence a kernel of index two.
-- 4-7: RELATED: normal closures and sign determine the subgroup generated by k-cycles.
#check Equiv.Perm.alternatingGroup_le_of_normal
-- 4-8: RELATED: |GL3(F2)| = 168 and its action on seven nonzero vectors;
-- GAP for the conjugacy-class calculation and complete simplicity argument in the exercise.
-- The missing work counts the conjugacy classes in GL₃(𝔽₂) ≅ PSL₂(𝔽₇), uses
-- its action on seven nonzero vectors, and proves the resulting simple-group claim.
#check Matrix.card_GL_field
-- 4-9: RELATED: cyclic automorphism group forces cyclic central quotient, hence commutativity.
#check commutative_of_cyclic_center_quotient
-- GAP: the finite-group cyclicity conclusion as a dedicated theorem.
-- The missing finite argument uses the hypothesis Aut(G) cyclic twice: it first
-- forces G/Z(G) cyclic and hence G abelian, then rules out every finite abelian
-- noncyclic p-primary factor, leaving G cyclic.
-- 4-10: adjacent transpositions generate; the star-transposition version follows similarly.
#check Equiv.Perm.mclosure_swap_castSucc_succ
-- 4-11, 4-12: GAP: splitting conjugacy classes in normal subgroups, the distinct-odd-parts
-- criterion for A_n, and the explicit class tables for A4,A5,A6,A7.
-- Missing are the criterion for an S_n class to split in A_n, its distinct odd
-- cycle-length condition, and the concrete conjugacy-class/count tables for
-- A₄, A₅, A₆, and A₇.
-- 4-13: GAP: the Todd-Coxeter worked example (group of order six).
-- No verified coset-enumeration trace is packaged for the given presentation:
-- the exercise wants the table deductions that establish the six cosets and
-- identify the resulting group.
-- 4-14: primitivity implies quasiprimitivity (nontrivial normal subgroups act transitively).
#check MulAction.IsPreprimitive.isQuasiPreprimitive
-- 4-15: RELATED: uniqueness of the index-two subgroup of S4.
#check Equiv.Perm.eq_alternatingGroup_of_index_eq_two
-- GAP: all element counts and the nonexistence of an order-six subgroup of A4 in one package.
-- Missing are the explicit counts of elements of each order in A₄ and the
-- subgroup-order argument ruling out a subgroup of order six, as one worked API.
-- 4-16: RELATED: faithful coset action, factorial divisibility, and simplicity of A5.
#check Subgroup.normalCore_eq_ker
#check alternatingGroup.isSimpleGroup_five
-- 4-17: GAP: the explicit S_n embedding into A_(n+2).
-- The absent construction sends each permutation to an even permutation on two
-- added points, proving an injective homomorphism S_n ↪ A_{n+2}.
-- 4-18: double cosets, their partition and cardinalities.
#check DoubleCoset.doubleCoset
#check DoubleCoset.Quotient
#check DoubleCoset.iUnion_quotToDoubleCoset
-- RELATED: the double-coset API supplies the partition argument; see its card lemmas.
-- 4-19: GAP: characterization of normal subgroups by fixed points in every transitive action.
-- The exact missing equivalence says: for every transitive G-set X, N fixes one
-- point iff N fixes every point, precisely when N is normal in G. Equivalently,
-- its fixed-point set is either empty or all of X. A requirement of a fixed
-- point in every action would instead force N=1 by considering the regular action.
-- 4-20: RELATED: categorical group actions; GAP for this exact automorphism-of-forgetful-functor API.
-- The missing categorical theorem identifies natural automorphisms of the
-- forgetful functor from G-sets with elements of G, including compatibility
-- across all G-sets required by the exercise.
#check Action

-- 5-1: a torsion-count bound implies cyclicity even without assuming commutativity.
#check isCyclic_of_card_pow_eq_one_le
-- 6-1: GAP: restricting a composition series to a normal subgroup and deleting repetitions.
-- Missing is the explicit refinement theorem: intersect a finite composition
-- series G = G₀ ▹ ⋯ ▹ 1 with N, delete equal consecutive intersections, and prove
-- that each remaining factor is simple.
-- 6-2: GAP: D4 and Q8 have the same derived subgroup/abelianization but are not isomorphic.
-- The missing counterexample computes D₄′ ≅ Q₈′ ≅ C₂ and both abelianizations
-- ≅ C₂ × C₂, then separates the groups by their element orders or subgroup
-- structure.
-- 7-1: RELATED: left ideals and matrix linear maps; GAP for this annihilator-matrix classification.
-- The missing classification proves every left ideal of M_n(F) is exactly
-- {M | MC = 0} for some n×r matrix C, not merely that this set is a left ideal.
#check Ideal
#check Matrix.toLin'
-- 7-2: reconstruction from the tensor category of finite-dimensional representations.
#check TannakaDuality.FiniteGroup.equiv
#check TannakaDuality.FiniteGroup.rightRegular
#check TannakaDuality.FiniteGroup.mulRepHom
-- These implement the reconstruction and its regular-representation ingredients.
-- Caution: 7-2(b) needs algebra automorphisms, not arbitrary endomorphisms;
-- the individual coordinate factors are ideals, not unital subalgebras of the product.
-- 7-2(d)'s f(gg') is a right-action convention; Mathlib's rightRegular uses f(g'g).

-- Appendix A. Additional exercises (the source starts at 34 and omits 36).

-- A34: GAP: a finite group with one maximal subgroup is a cyclic p-group.
-- Missing implication: uniqueness of a maximal proper subgroup yields a prime p
-- and n ≥ 1 with G ≃ C_(p^n); neither cyclicity nor the prime-power cardinality
-- is supplied by a theorem about maximal subgroups alone.
-- A35: RELATED: commuting permutations of order 146 in S76 and the possible product orders.
#check Equiv.Perm.lcm_cycleType
#check Commute.orderOf_mul_dvd_lcm
-- GAP: the specific enumeration of possible orders.
-- Missing calculation: commuting order-146 permutations on 76 letters have a common
-- 73-point orbit and involutions on the remaining three points. Their product has
-- order 1 or 73, and both occur; the lcm bound alone also permits 2 and 146.
-- A37(a), A48: RELATED: generating the derived subgroup from conjugation-stable generators;
-- for involutions, commutators of generators are squares of pairwise products.
#check Subgroup.commutator
-- GAP: the exact generating-set equalities and A37(b)'s index-at-most-two assertion.
-- Missing statements: if X generates G and is stable under conjugation, [G,G]
-- equals the subgroup generated by [x,y] for x,y ∈ X; for involutions these are (xy)².
-- Separately, for any involution generating set, the subgroup generated by all xy
-- has index at most two. The commutator construction does not package these reductions.
-- A38: GAP: groups of order p(2p-1), with both factors prime, are commutative.
-- The hypotheses include p ≥ 3. Missing specialization of the order-pq classification:
-- with q=2p-1, p does not divide q-1, so the nontrivial semidirect-product case
-- cannot occur and every such group is cyclic (hence commutative).
-- A39: RELATED: Sylow intersections require conjugating P; see 5.12.
-- GAP: the overgroup-normalizer assertion and infinite-subgroup counterexample; see 6.19,1.33.
-- Missing finite statement: N_G(P) ≤ H for Sylow P implies N_G(H)=H.
-- The infinite counterexample must exhibit gHg⁻¹ properly contained in H, so that
-- containment cannot replace equality in the definition of a normalizer.
-- A40: GAP: nonsimplicity of order 616.
-- Missing theorem: Nat.card G = 616 = 8·7·11 implies a nontrivial proper normal
-- subgroup. Sylow counting supplies numerical constraints, but the contradiction
-- under a simplicity assumption is not assembled for this cardinality.
-- A41: RELATED: centralizer of a k-cycle, and the normalizer action on its cyclic subgroup.
#check Subgroup.centralizer
#check Subgroup.normalizer
#check IsCyclic.card_mulAut
-- GAP: the two explicit factorial/totient order formulas.
-- For a k-cycle with k ≥ 2, the requested orders are k·(n-k)! for the centralizer
-- and k·φ(k)·(n-k)! for the normalizer: include arbitrary permutations off the support
-- and realize every automorphism of the cyclic subgroup. At k=1 both groups are S_n;
-- the general subgroup constructors do not compute these orders.
-- A42: GAP: counterexample to equivalence of gHg⁻¹ ⊆ H and g⁻¹Hg ⊆ H for infinite groups.
-- Missing explicit witness: take H to be the integer translations of Q and g the
-- dilation x ↦ 2x in its affine group. Then gHg⁻¹ is the even translations,
-- whereas g⁻¹Hg includes half-integer translations and is not contained in H.
-- A43(a): fixed-point-free automorphisms give bijective commutator maps.
#check MonoidHom.FixedPointFree.commutatorMap_injective
#check MonoidHom.FixedPointFree.commutatorMap_surjective
-- RELATED: compose with inversion/conjugation to match the exercise's orientation.
-- A43(b): GAP: the coset equal-order conclusion as a standalone theorem.
-- With H finite and normal, orderOf g=n, and C_H(g)={1}, every element of gH
-- should have order n. The bijective commutator map above must be used to show
-- that every element of this coset is H-conjugate to g, then transfer its order.
-- A44: RELATED: conjugate stabilizers have conjugate normalizers and equal cardinalities.
#check MulAction.stabilizer_smul_eq_stabilizer_map_conj
-- A45: normal abelian Sylow subgroups give an abelian direct product.
#check Sylow.directProductOfNormal
-- A46: GAP: finiteness criterion for ⟨a,b | a³=b², a^m=b^n=1⟩.
-- Missing parameter classification: for positive m,n, determine when an infinite
-- group generated by a,b can satisfy these relations, and prove finiteness in all
-- other cases. A presentation type alone provides neither the criterion nor witnesses.
-- A47: GAP: ⟨x,y | x²=y³=(xy)⁴=1⟩ and its derived series (S4).
-- Missing isomorphism from this presentation to S4, including an upper bound of 24
-- from the relations. Then identify the derived series as S4, A4, V4, 1,
-- giving cardinalities 24,12,4,1 and solvability of derived length three.
-- A48: see A37 above.
-- A49: GAP: normalizer of the diagonal group modulo the diagonal group is S_n.
-- Caution: additional hypotheses on F are needed; over F2 the diagonal group is trivial.
-- For |F|>2, the missing description is the group of monomial matrices:
-- a unique diagonal matrix times a permutation matrix, with quotient map to S_n
-- and kernel the diagonal subgroup. Over F2, its normalizer is all GL_n(F2),
-- so the source's unrestricted assertion cannot be used as stated.
-- A50: GAP: abelianization index of ⟨x,y | x²=y⁵=(xy)⁴=1⟩.
-- Missing calculation: after abelianizing, 2x=0, 5y=0 and 4(x+y)=0 force y=0;
-- mapping x to the generator of C2 proves the abelianization is exactly C2.
-- Thus [G:G′]=2, even without determining the order of G.
-- A51: GAP: quotient by the subgroup generated by odd-order elements is a 2-group.
-- Missing package: this generating set is conjugation invariant, its closure H is
-- normal, and |G/H|=2^n for some n. This requires showing every odd-primary part
-- dies in the quotient, not just constructing the subgroup or quotient.
-- A52: RELATED: overgroups of a Sylow normalizer (6.19) and fixed-point congruences (5.1).
-- GAP: the combined self-normalizing and index ≡ 1 mod p theorem.
-- Given finite G, Sylow P and N_G(P) ≤ H ≤ G, conclude both N_G(H)=H
-- and [G:H] ≡ 1 mod p. The fixed-point congruence still needs the argument
-- identifying the P-fixed cosets and proving the normalizer assertion for H.
-- A53: GAP: solvability of groups of order 33·25.
-- Missing specialization at |G|=825: first produce a normal subgroup of order 11,
-- then prove the quotient of order 75 is solvable and lift solvability through
-- the extension. The numerical Sylow and extension arguments are not bundled.
-- A54: GAP: a surjective endomorphism centralizing inner automorphisms of a perfect group is identity.
-- Precisely: α : G →* G is surjective, α ∘ conj(g)=conj(g) ∘ α for every g,
-- and [G,G]=G; conclude α=id. Missing bridge: surjectivity makes α(g)g⁻¹ central,
-- so α fixes all commutators, which generate a perfect group.
-- A55: RELATED: groups generated by two involutions are dihedral quotients.
#check DihedralGroup
-- GAP: all six requested subgroup, centralizer and conjugacy classifications.
-- Missing: identify G generated by involutions s,t with D_n via the rotation st.
-- For n odd, list rotation conjugacy pairs and the single reflection class,
-- their centralizers, and cyclic/dihedral subgroups indexed by divisors of n.
-- The final conjugacy assertion needs equal-order p-subgroups: as printed,
-- “any two p-subgroups” is false when their orders differ.
-- A56: RELATED: normal-subgroup orbit quotients inherit an action.
#check MulAction.orbitRel
-- GAP: equal orbit cardinalities and the nonnormal counterexample in the exercise.
-- For transitive G ↷ X and N normal, missing theorem: G acts transitively on
-- the set of N-orbits and translation gives bijections between any two N-orbits.
-- Without normality, ⟨(12)⟩ acting on {1,2,3} inside S3 has orbit sizes 2 and 1.
-- A57: RELATED: maximal subgroups of finite p-groups are normal, via nilpotency.
#check Group.isNilpotent_of_finite_tfae
-- GAP: the prime-index conclusion as part of this specific statement.
-- For each maximal proper M in a finite p-group, conclude M is normal and
-- [G:M]=p. Normality from nilpotency must be combined with the fact that
-- the quotient has no proper nontrivial subgroup and has prime-power order.
-- A58: GAP: metacyclic groups and their closure under subgroups/quotients; failure for products.
-- Missing predicate/package: ∃ N normal, N cyclic and G/N cyclic; transfer it
-- to subgroups and quotient groups. For failure of product closure, C_p² is
-- metacyclic but C_p² × C_p² is not: quotienting a cyclic subgroup leaves rank ≥ 3.
-- A59: double transitivity implies primitive and quasiprimitive action.
#check MulAction.isPreprimitive_of_is_two_pretransitive
#check MulAction.IsPreprimitive.isQuasiPreprimitive
-- A60: GAP: the order calculation for xyx⁻¹=y⁵ with order(x)=3 and odd order(y).
-- Missing deduction: conjugating three times gives y=y^125, so orderOf y divides
-- 124. Since y≠1 and its order is odd, orderOf y=31. The general order/divisibility
-- APIs do not combine these hypotheses into this numerical conclusion.
-- A61: RELATED: Iwasawa's simplicity criterion.
#check MulAction.IwasawaStructure
#check MulAction.IwasawaStructure.isSimpleGroup
-- GAP: the exact maximal-subgroup / normal-closure formulation of both parts.
-- Given maximal proper H, A normal in H and normalClosure(A)=G, part (a)
-- asks that N normal in G implies N≤H or G=NA. If G is perfect and A abelian,
-- part (b) concludes G/core(H) is simple. The action-based Iwasawa structure
-- still needs construction from these subgroup data and identification of its kernel.
-- A62: RELATED: the centre of a nonabelian p³ group; GAP for equality |Z|=p
-- and the explicit order-16 example with noncyclic centre.
-- The p-group centre theorem gives a positive prime-power order, not the exact
-- exponent one under the additional nonabelian/cardinality-p³ hypotheses.
-- For part (b), D4 × C2 has order 16 and centre C2 × C2; the missing item is
-- verification of that concrete example and its centre identification.
#check IsPGroup.card_center_eq_prime_pow
-- A63: GAP: the explicit presentation ⟨α,β | α²=β²=(αβ)³=1⟩ ≃ S3.
-- Missing equivalence sending α to (12) and β to (23): verify relations,
-- surjectivity, and injectivity by reducing every word to one of six normal forms.
-- A homomorphism out of PresentedGroup alone establishes only the first step.
-- A64: GAP: normal order-15 subgroup and the nonnilpotent counterexample at order 30.
-- Missing universal theorem: every order-30 group contains a normal subgroup
-- of order 15. For the second claim, verify S3 × C5 has order 30 and is not
-- nilpotent, for example by projecting onto the nonnilpotent quotient S3.
-- A65: GAP: finiteness and order of ⟨x,y | xyx⁻¹=y^t, x³=1⟩ as t varies.
-- Missing classification for integer t: t=1 gives C3 × Z and is infinite;
-- otherwise |G|=3·|t³-1|, realized as C_|t³-1| ⋊ C3 with action y ↦ y^t.
-- Prove both the upper bound from normal forms and the matching semidirect model.
-- A66: RELATED: order-pq classification (5.14); GAP for its solvability and
-- nilpotent iff abelian iff cyclic package.
-- For distinct primes p,q and |G|=pq, missing combined result: G is solvable,
-- and nilpotency, commutativity and cyclicity are equivalent. Include a nonnilpotent
-- example (S3 at order six), since solvability alone does not imply these conditions.
-- A67: GAP: Sylow p-subgroups are transitive on transitive G-sets of cardinality p^n.
-- For finite G, finite transitive X with |X|=p^n, and every Sylow P, the restricted
-- action P ↷ X should be transitive. Missing link: choose a Sylow subgroup of
-- a point stabilizer, extend it to G, and use orbit-stabilizer and Sylow conjugacy.
-- A68: GAP: order and derived series of the specified three-generator order-16 presentation.
-- Relations: bc=cb, a⁴=b²=c²=1, aca⁻¹=c, aba⁻¹=bc.
-- Missing normal-form/model proof that |G|=16 and c≠1; then [G,G]=⟨c⟩≃C2
-- and the next derived subgroup is trivial. This includes proving the presentation
-- has not collapsed to a smaller quotient.
-- A69: GAP: nontrivial normal subgroups of nilpotent groups meet the centre nontrivially.
-- Missing statement: if G is nilpotent and N normal with N≠1, then
-- N ∩ Z(G)≠1, without a finiteness assumption. A nontrivial-centre theorem for G
-- alone does not guarantee its intersection with a prescribed normal subgroup.
-- A70: RELATED: Sylow restriction and |GL_n(F_p)| (5.12,5.3);
-- GAP: the whole alternate proof via upper-unitriangular matrices without invoking Sylow.
-- Missing proof route: obtain a Sylow subgroup of H as H∩gPg⁻¹, count the
-- upper-unitriangular subgroup of GL_n(F_p), and embed an arbitrary finite group
-- into such a linear group to deduce Sylow existence. Existing Sylow lemmas prove
-- the conclusions but do not certify the requested independence from Sylow's theorems.
-- A71: split coprime extension with cyclic quotient (Schur-Zassenhaus).
#check Subgroup.exists_right_complement'_of_coprime
-- Source typo: coprimality should be with |H|; coprimality of |G/H| with |G| forces |G/H|=1.
-- A72: GAP: minimal normal subgroups of finite solvable groups are elementary abelian.
-- For a minimal nontrivial normal H in finite solvable G, missing conclusion:
-- H ≃ (C_p)^r for some prime p and r≥1. This needs the characteristic-subgroup
-- arguments forcing H abelian, then p-primary, then exponent p, and the final
-- vector-space/direct-product identification.
-- A73(a): finite-index intersections, and passage to a larger subgroup.
variable (G : Type*) [Group G] (H K : Subgroup G) [H.FiniteIndex] [K.FiniteIndex] in
#synth (H ⊓ K).FiniteIndex
#check Subgroup.finiteIndex_of_le
-- A73(b): GAP: the normal subgroup of FC-elements as a dedicated construction.
-- Missing subgroup FC(G)={g | [G:C_G(g)] is finite}, with multiplication/inverse
-- closure and normality under conjugation. The finite-index intersection APIs
-- above supply part of the closure proof but do not bundle this subgroup.
-- A74: GAP: groups of order p²q² (p>q) have a nontrivial normal p-subgroup.
-- Missing theorem with distinct primes p>q: ∃ N normal in G with |N|=p^r,
-- 1≤r≤2. This is weaker than normality of a Sylow p-subgroup; the proof must
-- also handle the exceptional Sylow-count case rather than assume uniqueness.
-- A75: GAP: generation modulo the derived subgroup and the nilpotent extension criterion.
-- Part (a): for finite nilpotent K, L≤K and L[K,K]=K imply L=K.
-- Part (b): for finite G and H≤G with [H,H] normal in G, nilpotency of H
-- and G/[H,H] implies nilpotency of G. The quotient notation requires that
-- normality hypothesis; arbitrary extensions of nilpotent groups do not suffice.
-- A76: GAP: the stated equivalence concerning abelian maximal subgroups in a noncyclic p-group.
-- Missing equivalence for finite noncyclic p-groups: [G:Z(G)]≤p² iff every
-- maximal subgroup is abelian iff at least two distinct maximal subgroups are
-- abelian. General maximal-subgroup normality does not give these centre bounds.
-- A77: GAP: semidirect decomposition and two nonabelian examples of order 56.
-- Missing theorem: every order-56 group has a proper nontrivial normal factor
-- and a complementary subgroup. Also construct two nonisomorphic nonabelian
-- examples and an invariant distinguishing them, e.g. D7 × C4 and D7 × C2²,
-- distinguished by existence of an element of order four.
-- A78: GAP: stable image/kernel decomposition for endomorphisms of finite groups,
-- and a counterexample to normality of the stable image.
-- Choose n with image(φ^m)=image(φ^n) for all m≥n; prove φ^n is an
-- automorphism on its image and G=ker(φ^n) ⋊ image(φ^n). A retraction
-- S3 → C2 → S3 (sign followed by a transposition inclusion) supplies a stable
-- image that is not normal. Missing is this complete finite-group decomposition.
-- A79: same conjugacy-representative generation problem as 4-3.
-- A80: RELATED: the derived series stabilizes in a finite group; GAP for the
-- packaged characteristic perfect residual with universal solvable quotient.
-- Missing construction of the unique least normal K with solvable G/K, obtained
-- as the stabilized derived subgroup. Prove K characteristic, [K,K]=K,
-- and K≤N whenever G/N is solvable; consequently a solvable K must be trivial.
-- The derivedSeries APIs alone do not bundle stabilization and this universal property.
#check derivedSeries
#check derivedSeries_characteristic

-- Appendix B. Solutions to chapter exercises.
-- Indexed at 1-1 through 7-2 above; repeated arguments use the same APIs.
-- GAP: explicit worked calculations and tables are indicated at their exercise entries.
-- This refers to the remaining presentation identifications, concrete subgroup and
-- character tables, and counterexamples described at the corresponding GAP entries.
-- It is not a separate missing theorem: an abstract API match does not itself
-- verify the numerical or explicit computations in the supplied solutions.
-- Historical quotations, bibliography and index have no additional mathematical API entries.

-- Appendix C. Two-hour examination (and its solutions).
-- C1(a): GAP: the C2 * C3 counterexample to a²=b³=1 forcing (ab)⁶=1 (2.10).
-- Missing normal-form proof that the product of the two standard generators has
-- infinite order in the free product, although they have orders two and three.
-- For the reverse implication in the printed equivalence, b=a⁻¹ gives ab=1
-- with no restriction forcing a²=1 or b³=1.
-- C1(b): conjugacy of the two displayed S7 permutations follows from cycle type (4,3).
#check Equiv.Perm.isConj_iff_cycleType_eq
-- C1(c): GAP: cancellation of an A594 direct factor, using Krull-Schmidt (6.31).
-- Missing finite-group cancellation: G × A594 ≃ H × A594 implies G ≃ H.
-- This requires uniqueness of directly indecomposable factors (or a separate
-- cancellation theorem), not merely associativity and commutativity of products.
-- C1(d): RELATED: ⟨(123)⟩ is a proper subgroup of A5.
#check Subgroup.zpowers
-- C1(e): cyclic implies abelian implies nilpotent implies solvable; converses fail.
#check IsCyclic.commGroup
#check CommGroup.isNilpotent
#check IsNilpotent.to_isSolvable
-- C2: RELATED: Sylow counting and Schur-Zassenhaus at order 110.
#check card_sylow_modEq_one
#check Subgroup.exists_right_complement'_of_coprime
-- GAP: complete classification of those semidirect products.
-- Missing order-110 classification: the Sylow 11-subgroup is unique, and each
-- group is C11 ⋊ H with H≃C10 or D5. Classify actions H → Aut(C11)≃C10
-- up to isomorphism and distinguish the resulting groups; Schur-Zassenhaus
-- guarantees the order-ten complement but does not classify the actions.
-- C3: GAP: cyclic abelianization implies cyclicity for finite nilpotent groups; S3 is a counterexample
-- without nilpotency.
-- Missing theorem: for finite nilpotent G, IsCyclic(G/[G,G]) implies IsCyclic G
-- (equivalently, every abelian quotient is cyclic). The counterexample requires
-- identifying S3/[S3,S3]≃C2 while S3 itself is not cyclic.
-- C4: GAP: sharp 3^(n/3) bound for abelian subgroups of S_n, its construction, and the
-- regular-action bound |G| ≤ |X| used in the proof.
-- Missing package: a faithful transitive abelian action has trivial stabilizers;
-- disjoint 3-cycles give C3^m ≤ S_(3m) of order 3^m; and decomposing arbitrary
-- abelian permutation groups into orbits gives |G|≤3^(n/3). Equality is attained
-- when 3 divides n; the bound is not an exact maximum for every n.
-- C5: RELATED: extend conjugation to normal H; innerness gives G = H N_G(P).
#check MulAut.conjNormal
-- GAP: this exact normalizer factorization theorem.
-- For H normal in G, P≤H and every automorphism of H inner, conclude
-- every g∈G can be written h·u with h∈H and u∈N_G(P). The conjugation API
-- gives an automorphism of H; the missing step chooses its inner representative
-- and turns equality of conjugations into membership in the normalizer.
-- C6: GAP: identifying the two given presentations as Z ⋊ Z and Q8, respectively.
-- Part (a), yxy⁻¹=x⁻¹: prove unique normal forms x^i y^j (i,j∈Z) and the
-- equivalence with the semidirect product where the second Z acts by inversion.
-- Part (b) adds xyx⁻¹=y⁻¹: derive x²=y² and x⁴=y⁴=1, then prove the
-- presentation is exactly Q8, not just a quotient of it, using a matching model.
