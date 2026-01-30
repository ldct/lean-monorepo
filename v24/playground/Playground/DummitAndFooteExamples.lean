import Mathlib

set_option linter.style.longLine false

/-
# Chapter 1.1
-/

#check Group
#check CommGroup
#check AddGroup
#check AddCommGroup

/-
To see if Mathlib knows that ℤ forms an additive group, you can run

#synth AddGroup ℤ

For this file, we will use `inferInstance` to avoid printing the message.
-/
instance : AddGroup ℤ := inferInstance
instance : AddGroup ℚ := inferInstance
instance : AddGroup ℝ := inferInstance
noncomputable instance : AddGroup ℂ := inferInstance
instance : Group ℚˣ := inferInstance
instance : Group ℝˣ := inferInstance
instance : Group ℂˣ := inferInstance

/-
ℚˣ is defined as the group of units (invertible elements), but D&F define it as ℚ - {0}.
-/
example : ℚˣ = { q : ℚ | q ≠ 0 } := by sorry
example : ℝˣ = { r : ℝ | r ≠ 0 } := by sorry
example : ℂˣ = { c : ℂ | c ≠ 0 } := by sorry

/-
D&F define ℚ+ as the set of strictly positive rationals. This doesn't really exist in Mathlib (the closest thing is ℚ≥0, which includes 0).
-/
def PRat := {q : ℚ // 0 < q}
instance : Mul PRat where
  mul q r := ⟨q.val * r.val, by simp [q.property, r.property]⟩
lemma mul_val (q r : PRat) : (q * r).val = q.val * r.val := rfl
instance : One PRat where one := ⟨1, by positivity⟩
lemma one_val : (1 : PRat).val = 1 := rfl
instance : Inv PRat where
  inv q := ⟨q.val⁻¹, by simp [q.property]⟩
lemma inv_val (q : PRat) : (q⁻¹).val = q.val⁻¹ := rfl
instance : Group PRat := Group.ofLeftAxioms
  (by
    intro a b c
    have : 1 = 1 := by sorry
    apply Subtype.eq

    simp [mul_val, Rat.mul_assoc]
  ) (by
    intro a
    apply Subtype.eq
    simp [mul_val]
  ) (by
    intro a
    apply Subtype.eq
    simp [mul_val, inv_val]
    have := a.property
    field_simp
  )
/-
ℝ+ omitted
ℤ+ - show that Units ℤ is not ℤ - {0}
-/

instance {n : ℕ} : AddGroup (ZMod n) := inferInstance
example {n : ℕ} [NeZero n] : Fintype.card (ZMod n) = n := by simp
example : Nat.card (ZMod 0) = 0 := by simp

instance {n : ℕ} : Group (ZMod n)ˣ := inferInstance

instance {G H} [Group G] [Group H] : Group (G × H) := inferInstance

/-
Order. Mathlib defines this for monoids
-/

example {G} [Group G] (g : G) : orderOf g = 1 ↔ g = 1 := by simp

/-
In the additive group ... every nonzero element has infinite order.
-/
example : addOrderOf (1 : ℤ) = 0 := by simp [isOfFinAddOrder_iff_nsmul_eq_zero]

example : orderOf (1 : ℚ) = 1 := by simp
example : orderOf (-1 : ℚ) = 2 := by simp
example : orderOf (2 : ℚ) = 0 := by
  simp only [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one]
  rintro ⟨ n, hn, hn' ⟩
  rcases n with ( _ | _ | n ) <;> simp_all
  norm_cast at hn'
  grind


example : addOrderOf (6 : ZMod 9) = 3 := by simp +decide [addOrderOf_eq_iff]
example : orderOf (2 : ZMod 7) = 3 := by simp +decide [orderOf_eq_iff]
/-
# Chapter 1.2 - Dihedral groups
-/



/-
# Chapter 1.3 - Symmetric groups
-/

/-
# Quaternion group
-/
abbrev Q := QuaternionGroup 2

def Q.one := (QuaternionGroup.a 0 : Q)
def Q.I := (QuaternionGroup.a 1 : Q)
def Q.J := (QuaternionGroup.xa 0 : Q)
def Q.K := (QuaternionGroup.xa 3 : Q)

instance : Neg Q where
  neg q := q * (QuaternionGroup.a (2 : ZMod 4))

example : Q.I^2 = -1 := by decide
example : Q.J^2 = -1 := by decide
example : Q.K^2 = -1 := by decide
example : Q.I * Q.J = Q.K := by decide
example : Q.J * Q.I = -Q.K := by decide
example : Q.I * Q.K = -Q.J := by decide
example : Q.J * Q.K = Q.I := by decide
example : Q.K * Q.J = -Q.I := by decide
example : Q.K * Q.I = Q.J := by decide
example : (-1 : Q)^2 = 1 := by decide
example : (-Q.I)^2 = -1 := by decide
example : (-Q.J)^2 = -1 := by decide
example : (-Q.K)^2 = -1 := by decide
example : -Q.I * Q.I = 1 := by decide
example : -Q.J * Q.J = 1 := by decide
example : -Q.K * Q.K = 1 := by decide
example : Q.I * -Q.I = 1 := by decide
example : Q.J * -Q.J = 1 := by decide
example : Q.K * -Q.K = 1 := by decide

/-
# Chapter 1.6 - Homomorphisms and isomorphisms
-/

variable {G H} [Group G] [Group H] in
/-- info: G →* H : Type (max u_1 u_2) -/ #guard_msgs in
#check G →* H

/-- info: MonoidHom.{u_10, u_11} (M : Type u_10) (N : Type u_11) [MulOne M] [MulOne N] : Type (max u_10 u_11) -/ #guard_msgs in
#check MonoidHom

/-- info: G ≃* H : Type (max u_2 u_1)-/ #guard_msgs in
variable {G H} [Group G] [Group H] in
#check G ≃* H

/-- info: MulEquiv.{u_9, u_10} (M : Type u_9) (N : Type u_10) [Mul M] [Mul N] : Type (max u_10 u_9) -/ #guard_msgs in
#check MulEquiv

/-
≃* bundles up the bijection and the homomorphism.
-/
def equivOfIso {G H} [Group G] [Group H] (φ : G ≃* H) : G ≃ H := φ.toEquiv
def homOfIso {G H} [Group G] [Group H] (φ : G ≃* H) : G →* H := φ.toMonoidHom

example {G} [Group G] : G ≃* G := {
  toFun := id
  invFun := id
  left_inv := by grind
  right_inv := by grind
  map_mul' := by grind
}


-- exp : ℝ → ℝ+ homomorphism from + to *

example {G H} [Group G] [Group H] (equiv : G ≃ H) : (Equiv.Perm G) ≃* (Equiv.Perm H) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

-- any non-abelian group of order 6 is isomorphic to s3

lemma cardinal_eq_of_iso {G H} [Group G] [Group H] (φ : G ≃* H) : Cardinal.mk G = Cardinal.mk H := Cardinal.mk_congr φ.toEquiv
lemma natcard_eq_of_iso {G H} [Group G] [Group H] (φ : G ≃* H) : Nat.card G = Nat.card H := by sorry

-- G is abelian iff H is abelian

example {G H} [Group G] [Group H] (φ : G ≃* H) (g : G) : orderOf g = orderOf (φ g) := by simp

/-
# Chapter 1.7 - Group actions
-/

/-
# Chapter 2.1 - Subgroups
-/

def IntSubgroupRat : AddSubgroup ℚ where
  carrier := { r | r : ℤ }
  add_mem' ha hb := by
    simp at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    norm_cast
  zero_mem' := by
    use 0
    norm_num
  neg_mem' ha := by
    simp at ha
    obtain ⟨ a, rfl ⟩ := ha
    use -a
    norm_cast

def RatSubgroupReal : AddSubgroup ℝ where
  carrier := { r | r : ℚ }
  add_mem' ha hb := by
    simp at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    norm_cast
  zero_mem' := by
    use 0
    norm_num
  neg_mem' ha := by
    simp at ha
    obtain ⟨ a, rfl ⟩ := ha
    use -a
    norm_cast

/-
D&F statement `ℤ ≤ ℚ ≤ ℝ` can have multiple formalizations. In particular we can treat `ℤ` and `ℚ` as subgroups of `ℝ`.
-/

def IntSubgroupReal : AddSubgroup ℝ where
  carrier := { r | r : ℤ }
  add_mem' ha hb := by
    simp at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    norm_cast
  zero_mem' := by
    use 0
    norm_num
  neg_mem' ha := by
    simp at ha
    obtain ⟨ a, rfl ⟩ := ha
    use -a
    norm_cast

example : IntSubgroupReal ≤ RatSubgroupReal := by
  simp [IntSubgroupReal, RatSubgroupReal]
  intro a
  use a
  norm_cast

/-
# Chapter 2.2 - Centralizers and normalizers, stabalizers and kernels
-/

/-
# Chapter 2.3 - Cyclic groups and cyclic subgroups
-/

#check IsCyclic
#check IsAddCyclic

def IsCyclicSubgroup {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ r₀ ∈ H, ∀ h ∈ H, ∃ n : ℤ, h = r₀ ^ n

def rotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := { DihedralGroup.r i | i : ZMod n }
  mul_mem' := by
    rintro a b ⟨ i1, rfl ⟩ ⟨ i2, rfl ⟩
    use i1 + i2
    rfl
  one_mem' := by
    use 0
    rfl
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    use -i
    rfl

-- Note that this casts `rotations` to a type
example (n : ℕ) : IsCyclic (rotations n) := by
  use ⟨ DihedralGroup.r 1, by use 1 ⟩
  sorry

example (n : ℕ) : IsCyclicSubgroup (rotations n) := by
  use DihedralGroup.r 1
  constructor
  · use 1
  intro h hh
  sorry

/-
# Chapter 2.4
-/

#check Subgroup.closure

/-
# Chapter 2.5 Lattice
-/

#check Subgroup.instCompleteLattice

abbrev ℤ4 := ZMod 4

def g1 : AddSubgroup ℤ4 := ⊥
example : g1.carrier = {0} := by simp [g1]; rfl

def g2 : AddSubgroup ℤ4 where
  carrier := { 0, 2 }
  add_mem' := by decide
  zero_mem' := by decide
  neg_mem' := by decide

def g3 : AddSubgroup ℤ4 := ⊤
example : g3.carrier = {0, 1, 2, 3} := by
  simp [g3]
  sorry

example : g1 < g2 := by
  apply lt_of_le_of_ne
  · simp [g1, g2]
  · sorry

example : g2 < g3 := by
  apply lt_of_le_of_ne
  · simp [g2, g3]
  · sorry


instance {G} [Group G] : CompleteLattice (Subgroup G) := inferInstance

/-
# Chapter 3.1
-/

example {n : ℕ} : ℤ →+ ZMod n where
  toFun := fun i => i
  map_zero' := by norm_cast
  map_add' := by grind

-- left cosets, right cosets

abbrev centerQ : Subgroup Q where
  carrier := { 1, -1 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

abbrev quotientGroup := Q ⧸ centerQ

example : (QuotientGroup.mk 1 : quotientGroup) = (QuotientGroup.mk (-1)) := by sorry

/-
# Chapter 3.3
-/

#check QuotientGroup.quotientKerEquivRange

/-
# Chapter 7.1
-/
#check Ring
#check NonUnitalRing
#check CommRing

instance : CommRing ℤ := inferInstance
instance : CommRing ℚ := inferInstance
instance : CommRing ℝ := inferInstance
instance : CommRing ℂ := inferInstance
instance {n : ℕ} : CommRing (ZMod n) := inferInstance

instance : Ring (Quaternion ℝ) := inferInstance
instance : Ring (Quaternion ℚ) := inferInstance

instance {X R : Type*} [NonUnitalRing R] : NonUnitalRing (X → R) := inferInstance
instance {X R : Type*} [Ring R] : Ring (X → R) := inferInstance
instance {X R : Type*} [CommRing R] : CommRing (X → R) := inferInstance

instance : Ring (ContinuousMap ℝ ℝ) := inferInstance

/-
It is more common to formalize 2ℤ as an ideal, but we can also define it as a nonunital ring.
-/
abbrev evenIntegers := {i : ℤ // Even i}
instance : Add evenIntegers where
  add a b := ⟨a.1 + b.1, by grind⟩
lemma add_val (a b : evenIntegers) : (a + b).val = a.val + b.val := rfl
instance : Zero evenIntegers where zero := ⟨0, by simp⟩
instance : Neg evenIntegers where neg a := ⟨-a.1, by sorry⟩
instance : NonUnitalRing evenIntegers where
  add_assoc := by
    intro a b c
    ext
    simp [add_val]
    grind
  add_comm := by sorry
  mul := by sorry
  mul_assoc := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  zero_add := by sorry
  add_zero := by sorry
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by sorry


variable {R} [Ring R] in
#synth Ring (R × R)


/-
# Chapter 7.3 - Ring homomorphisms and quotient rings
-/

/-
The ring homomorphism from ℤ to (ZMod 2) that sends an integer to 0 if it is even and 1 if it is odd.
-/
example : ℤ →+* (ZMod 2) where
  toFun := fun n => n
  map_one' := by norm_cast
  map_mul' x y := by norm_cast
  map_zero' := by norm_cast
  map_add' x y := by norm_cast

open Polynomial in
def evalAtZero : ℚ[X] →+* ℚ where
  toFun := fun p => p.eval 0
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp
example (a : Ideal ℤ) : a ⊔ a = a := by order
example (a : Ideal ℤ) : a + a = a := by
  rw [Submodule.add_eq_sup]
  order

-- Image of a ring homomorphism
example {R H} [Ring R] [Ring H] (φ : R →+* H) : Subring H := sorry

-- Kernel of a ring homomorphism
example {R H} [Ring R] [Ring H] (φ : R →+* H) : Ideal R := RingHom.ker φ

-- First isomorphism theorem for rings

/-
Given a ring `R`, the ideal `⊤` is the ideal of all elements of `R`, and the ideal `⊥` is the trivial ideal {0} (containing only the zero element).

The notation comes from the lattice structure on ideals, which will be defined later.
-/

example {R} [Ring R] : (⊤ : Ideal R).carrier = Set.univ := rfl
example {R} [Ring R] : (⊥ : Ideal R).carrier = {0} := rfl


/-
Reduction modulo n, the projection from ℤ to ℤ/nℤ. In mathlib ℤ/nℤ is represented as ZMod n.
-/
example {n : ℕ} : ℤ →+* (ZMod n) where
  toFun := fun n => n
  map_one' := by norm_cast
  map_mul' x y := by norm_cast
  map_zero' := by norm_cast
  map_add' x y := by norm_cast
#check Int.castRingHom (ZMod 3)

open Polynomial in
noncomputable def polyMod (n : ℕ) : ℤ[X] →+* (ZMod n)[X] where
  toFun := fun p => p.map (Int.castRingHom (ZMod n))
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp

open Polynomial in
example : polyMod 2 (X ^ 2 + 1) = X ^ 2 - 1 := by
  simp [polyMod]
  grind


def nℤ (n : ℤ) : Ideal ℤ where
  carrier := { n * i | i : ℤ }
  add_mem' ha hb := by
    simp at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    ring
  zero_mem' := by
    use 0
    norm_num
  smul_mem' c d hx := by
    simp at hx
    obtain ⟨ n, rfl ⟩ := hx
    use c * n
    grind [Int.zsmul_eq_mul]

example : Nonempty ((ℤ ⧸ nℤ 2) ≃+* (ZMod 2)) := by sorry

example {n : ℤ} : nℤ n = Ideal.span {n} := by
  ext x
  simp [nℤ, Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_right, eq_comm]

abbrev ℤ2ℤ : Ideal ℤ := Ideal.span {2}
abbrev ℤ3ℤ : Ideal ℤ := Ideal.span {3}

example : (nℤ 2) + (nℤ 3) = (nℤ 1) := by
  simp
  ext i
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, 2 * x + 3 * y = 1 := by
    exists 2, -1;
  have h_mul : 2 * (x * i) + 3 * (y * i) = i := by
    linear_combination' hxy * i
  have h_mem : i ∈ nℤ 2 ⊔ nℤ 3 := by
    exact h_mul ▸ Submodule.add_mem_sup ( ⟨ x * i, rfl ⟩ ) ( ⟨ y * i, rfl ⟩ )
  simp [h_mem]
  exact ⟨ i, by ring ⟩

example {n m : ℤ} : (nℤ n) + (nℤ m) = (nℤ (n.gcd m)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, b, hx_eq⟩ : ∃ a b : ℤ, x = n * a + m * b := by
      obtain ⟨ a, ha, b, hb, rfl ⟩ := Submodule.mem_sup.mp hx
      obtain ⟨ c, rfl ⟩ := ha; obtain ⟨ d, rfl ⟩ := hb; exact ⟨ c, d, by ring ⟩;
    exact ⟨ a * n / Int.gcd n m + b * m / Int.gcd n m, by nlinarith [ Int.ediv_mul_cancel ( show ( Int.gcd n m : ℤ ) ∣ a * n from dvd_mul_of_dvd_right ( Int.gcd_dvd_left _ _ ) _ ), Int.ediv_mul_cancel ( show ( Int.gcd n m : ℤ ) ∣ b * m from dvd_mul_of_dvd_right ( Int.gcd_dvd_right _ _ ) _ ) ] ⟩;
  · intro x hx ae
    -- By Bezout's identity, there exist integers $a$ and $b$ such that $an + bm = \gcd(n, m)$.
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * n + b * m = Int.gcd n m := by
      exact Int.gcd_eq_gcd_ab n m ▸ ⟨ Int.gcdA n m, Int.gcdB n m, by ring ⟩;
    -- Since $x \in nℤ (Int.gcd n m)$, we can write $x = k \cdot \gcd(n, m)$ for some integer $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, x = k * Int.gcd n m := by
      -- By definition of $nℤ$, if $x \in nℤ (Int.gcd n m)$, then there exists an integer $k$ such that $x = k * Int.gcd n m$.
      obtain ⟨k, hk⟩ := hx;
      use k;
      exact hk.symm.trans ( mul_comm _ _ );
    intro h; obtain ⟨ s, hs ⟩ := h
    simp_all
    rw [ ← hs ]
    exact Set.mem_iInter.mpr fun h => by
      convert s.smul_mem k ( s.add_mem ( s.smul_mem a ( h.1 <| Set.mem_setOf.mpr ⟨ 1, by ring ⟩ ) ) ( s.smul_mem b ( h.2 <| Set.mem_setOf.mpr ⟨ 1, by ring ⟩ ) ) ) using 1
      rw [ ← hab ]
      ring

example {n m : ℤ} : (nℤ n) * (nℤ m) = (nℤ (n * m)) := by
  have h_def : nℤ n = Ideal.span {n} ∧ nℤ m = Ideal.span {m} := by
    constructor <;> ext x <;> simp [ Ideal.mem_span_singleton ]
    · exact ⟨ fun ⟨ y, hy ⟩ => ⟨ y, by linarith ⟩, fun ⟨ y, hy ⟩ => ⟨ y, by linarith ⟩ ⟩
    · exact ⟨ fun ⟨ y, hy ⟩ => ⟨ y, by linarith ⟩, fun ⟨ y, hy ⟩ => ⟨ y, by linarith ⟩ ⟩

  have h_prod : Ideal.span {n} * Ideal.span {m} = Ideal.span {n * m} := Ideal.span_singleton_mul_span_singleton n m
  convert h_prod using 1
  · rw [ h_def.1, h_def.2 ]
  · have h_def : nℤ (n * m) = Ideal.span {n * m} := by
      have h_gen : ∀ k : ℤ, nℤ k = Ideal.span {k} := by
        intro k; ext; simp [nℤ];
        simp [ Ideal.mem_span_singleton ]
        exact ⟨ fun ⟨ i, hi ⟩ => ⟨ i, hi.symm ⟩, fun ⟨ i, hi ⟩ => ⟨ i, hi.symm ⟩ ⟩
      exact h_gen (n * m);
    exact h_def

example {n m : ℤ} : (nℤ n) ⊓ (nℤ m) = (nℤ (n.lcm m)) := by
  ext x
  have h_div : x ∈ nℤ n ⊓ nℤ m ↔ n ∣ x ∧ m ∣ x := by
    exact ⟨ fun h => ⟨ h.1.choose_spec.symm ▸ dvd_mul_right _ _, h.2.choose_spec.symm ▸ dvd_mul_right _ _ ⟩, fun h => ⟨ h.1.imp fun i hi => by linarith, h.2.imp fun i hi => by linarith ⟩ ⟩;
  have h_lcm_div : (n.lcm m : ℤ) ∣ x ↔ n ∣ x ∧ m ∣ x := by
    exact ⟨ fun h => ⟨ Int.dvd_trans ( Int.dvd_lcm_left _ _ ) h, Int.dvd_trans ( Int.dvd_lcm_right _ _ ) h ⟩, fun h => Int.coe_lcm_dvd h.1 h.2 ⟩;
  convert h_lcm_div using 1;
  · convert h_div using 1;
  · simp [ nℤ ]
    rw [ ← h_lcm_div, dvd_iff_exists_eq_mul_right ]
    simp [ eq_comm ]


example {R} [Ring R] (I J : Ideal R)
: (I + J).carrier = {i + j | (i ∈ I.carrier) (j ∈ J.carrier) } := by
  ext x
  simp [Submodule.mem_sup]

#check DualNumber ℤ

#check IsPrincipalIdealRing
