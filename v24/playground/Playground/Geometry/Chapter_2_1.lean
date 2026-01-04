import Mathlib

set_option linter.style.longLine false

/-
This file formalizes the definitions, theorems and exercises from Chapter 2.1 of Dummit and Foote (page 47).
-/

-- Definition, p46
@[to_additive] def IsSubgroup {G : Type} [Group G] (H : Set G) : Prop := H.Nonempty ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) ∧ ∀ x ∈ H, x⁻¹ ∈ H

-- Example 1: ℤ ≤ ℚ and ℚ ≤ ℝ with the operation of addition
example : IsAddSubgroup { (r : ℚ ) | r : ℤ} := by
  simp [IsAddSubgroup]
  and_intros
  · use 0
    simp
  · intro a b
    use a + b
    simp
  · intro a
    use -a
    simp

example : IsAddSubgroup { (r : ℝ ) | r : ℚ} := by
  simp [IsAddSubgroup]
  and_intros
  · use 0
    simp
  · intro a b
    use a + b
    simp
  · intro a
    use -a
    simp

-- Examples 2-5 are straightforward to formalize and verify. Example 6 is tricky because a subgroup is not a Group.

@[to_additive] lemma IsSubgroup.one_mem {G : Type} [Group G] (H : Set G) (h : IsSubgroup H) : 1 ∈ H := by
  obtain ⟨h_nonempty, mul_mem, inv_mem⟩ := h
  let g := h_nonempty.some
  have g_inv_in_H := inv_mem g h_nonempty.some_mem
  have := mul_mem g h_nonempty.some_mem g⁻¹ g_inv_in_H
  group at this
  exact this

-- Proposition 1, part 1 (Subgroup Criterion, general version)
@[to_additive] lemma SubgroupCriterion {G : Type} [Group G] (H : Set G)
: (IsSubgroup H) ↔ (H.Nonempty ∧ ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) := by
  constructor
  · rintro ⟨ h_nonempty, mul_mem, inv_mem ⟩
    simp_all
  · rintro ⟨ h1, h2 ⟩

    have one_in_H : 1 ∈ H := by
      have := h2 h1.some h1.some_mem h1.some h1.some_mem
      group at this
      exact this

    have h_inv_mem : ∀ x ∈ H, x⁻¹ ∈ H := by
      intro x hx
      have := h2 1 one_in_H x hx
      simp at this
      exact this


    and_intros <;> try assumption
    · intro x hx y hy
      have := h2 x hx y⁻¹ (h_inv_mem y hy)
      group at this
      exact this

-- Proposition 1, part 2 (Subgroup Criterion, finite groups)
lemma SubgroupCriterionFinite {G : Type} [Group G] [Fintype G] (H : Set G)
: (IsSubgroup H) ↔ (H.Nonempty ∧ ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) := by
  constructor
  · rintro ⟨ h_nonempty, mul_mem, inv_mem ⟩
    simp_all
  · rintro ⟨ h_nonempty, mul_mem ⟩
    admit

/-
Equivalence with Mathlib subgroups
-/

-- A set H satisfying IsSubgroup is the carrier of some Mathlib subgroup
@[to_additive] def Subgroup.ofIsSubgroup {G} [Group G] (H : Set G) (h : IsSubgroup H) : Subgroup G := {
  carrier := H
  mul_mem' := by
    intro a b ha hb
    simp [IsSubgroup] at h
    exact h.2.1 a ha b hb
  one_mem' := by
    exact IsSubgroup.one_mem H h
  inv_mem' := by
    have one_mem := IsSubgroup.one_mem H h
    have h' := h
    rw [SubgroupCriterion] at h
    obtain ⟨h_nonempty, inv_mem⟩ := h
    intro x hx
    specialize inv_mem 1 one_mem x hx
    group at *
    exact inv_mem
}

@[to_additive] def Subgroup.ofSubgroupCriterion {G} [Group G] (H : Set G) (h₁ : H.Nonempty) (h₂ : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) : Subgroup G
:= Subgroup.ofIsSubgroup H (by
  rw [SubgroupCriterion]
  exact ⟨ h₁, h₂ ⟩
)

@[to_additive] def Subgroup.ofSubgroupCriterionOne {G} [Group G] (H : Set G) (h : 1 ∈ H ∧ (∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H)) : Subgroup G
:= Subgroup.ofIsSubgroup H (by
  rw [SubgroupCriterion]
  constructor
  · use 1
    exact h.1
  · exact h.2
)

-- A mathlib subgroup's carrier satisfies IsSubgroup.
@[to_additive] lemma Subgroup.IsSubgroup {G} [Group G] (H : Subgroup G) : IsSubgroup H.carrier := by
  and_intros
  · use 1
    exact H.one_mem'
  · intro a ha b hb
    exact H.mul_mem' ha hb
  · intro a ha
    exact H.inv_mem ha

def IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

/-
Exercises
-/

-- Exercise 2.1.1.a
example : AddSubgroup ℂ := AddSubgroup.ofAddSubgroupCriterion
{ a + a*Complex.I | a : ℝ }
(by
  use 0+0*Complex.I
  simp
  use 0
  norm_num
)
(by
  rintro x hx y hy
  simp at *
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  use a - b
  simp
  ring
)

-- Exercise 2.1.1.b
example : Subgroup ℂˣ := Subgroup.ofSubgroupCriterion
  {x : ℂˣ | ‖x.val‖ = 1 }
  (by use 1; simp)
  (by intros; simp_all)

-- Exercise 2.1.1.c
example (n : PNat) : AddSubgroup ℚ := AddSubgroup.ofAddSubgroupCriterion
{ a | a.den ∣ n }
(by use 0; simp)
(by
  rintro x hx y hy
  simp at *
  have h_denom : (x + (-y)).den ∣ Nat.lcm x.den y.den :=
    Rat.add_den_dvd_lcm _ _
  exact h_denom.trans ( Nat.lcm_dvd hx hy )
)

-- Exercise 2.1.1.d
example (n : PNat) : AddSubgroup ℚ := AddSubgroup.ofAddSubgroupCriterion
{ a | a.den.Coprime n }
(by use 0; simp)
(by
  rintro x hx y hy
  simp at *
  have h_den : (x + -y).den ∣ x.den * y.den :=
    Rat.add_den_dvd _ _
  exact Nat.Coprime.coprime_dvd_left h_den ( Nat.Coprime.mul_left hx hy )
)

def Rational (x : ℝ) : Prop := ∃ q : ℚ, x = q

-- Exercise 2.1.1.e
example : Subgroup ℝˣ := Subgroup.ofSubgroupCriterion
  {x : ℝˣ | Rational (x^2) }
  (by use 1; simp [Rational]; use 1; norm_cast)
  (by
    rintro x hx y hy
    simp [Rational] at *
    obtain ⟨q₁, hq₁⟩ := hx
    obtain ⟨q₂, hq₂⟩ := hy
    use q₁ * q₂⁻¹
    ring_nf
    rw [hq₁]
    norm_cast
    rw [show y⁻¹^2 = (y^2)⁻¹ by rfl]
    push_cast at *
    rw [hq₂]
 )

lemma not_or3 (p q r : Prop) : ¬ (p ∧ q ∧ r) ↔ ¬ p ∨ ¬ q ∨ ¬ r := by grind

-- 2.1.2.d
example : ¬ IsAddSubgroup ({ 2*k + 1 | k : ℤ } ∪ { 0 }) := by
  rw [IsAddSubgroup, not_or3]
  right
  left
  simp
  use 1, 1
  grind

-- 2.1.3.a
open DihedralGroup in
example : Subgroup (DihedralGroup 4) := .ofSubgroupCriterionOne
  { r (0 : ZMod 4), r 2, sr 0, sr 2 }
  (by decide)

-- 2.1.3.b
open DihedralGroup in
example : Subgroup (DihedralGroup 4) := .ofSubgroupCriterionOne
  { r (0 : ZMod 4), r 2, sr 1, sr 3 }
  (by decide)

-- 2.1.4
example : ∃ (G : Type) (inst : AddGroup G) (H : Set G)
, (Nat.card H = 0) ∧ (∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) ∧ ¬ (@IsAddSubgroup G inst H) := by
  use ℤ, inferInstance, { z | z : ℕ }
  and_intros
  · rw [ Nat.card_eq_zero ];
    right
    exact Set.infinite_coe_iff.mpr <| Set.infinite_of_injective_forall_mem ( fun x y hxy => by simpa using hxy ) fun x => ⟨ x, rfl ⟩
  · intro x hx y hy
    simp at *
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    use a + b
    simp
  · rw [IsAddSubgroup, not_or3]
    right
    right
    push_neg
    use 1
    simp

-- Exercise 2.1.5
example {G : Type} [Group G] [Finite G] (H : Subgroup G)
: Nat.card H.carrier ≠ 0 := by
  have h_card_pos : 0 < Nat.card H := by
    norm_num
  exact ne_of_gt h_card_pos

example {G : Type} [Group G] [Finite G] (H : Subgroup G) (h : 2 < Nat.card G)
: Nat.card H.carrier ≠ (Nat.card G - 1)  := by sorry

-- 2.1.8
example {G : Type} [Group G] (H K : Set G) (h₁ : IsSubgroup H) (h₂ : IsSubgroup K)
: IsSubgroup (H ∪ K) ↔ (H ⊆ K ∨ K ⊆ H):= by
  constructor <;> intro h;
  · by_contra h_contra;
    -- Since $H$ and $K$ are subgroups, for any $h \in H$ and $k \in K$, we have $hk \in H \cup K$.
    have h_hk : ∀ h ∈ H, ∀ k ∈ K, h * k ∈ H ∪ K := by
      exact fun x hx y hy => h.2.1 x ( Or.inl hx ) y ( Or.inr hy );
    -- Let $h \in H \setminus K$ and $k \in K \setminus H$.
    obtain ⟨h, hhH, hhK⟩ : ∃ h ∈ H, h ∉ K := by
      exact Set.not_subset.mp fun h => h_contra <| Or.inl h
    obtain ⟨k, hkK, hkH⟩ : ∃ k ∈ K, k ∉ H := by
      exact Set.not_subset.mp fun h => h_contra <| Or.inr h;
    cases h_hk _ hhH _ hkK <;> simp_all
    · have := h₁.2.2 _ ‹_›; simp_all;
      have := h₁.2.1 _ this _ hhH; simp_all ;
      have := h₁.2.2 _ this; simp_all ;
    · simp_all +decide [ IsSubgroup ];
      have := h₂.2.1 _ ‹_› _ ( h₂.2.2 _ hkK ) ; simp_all ;
  · cases' h with h h;
    · rw [ Set.union_eq_right.mpr h ] ; exact h₂;
    · rw [ Set.union_eq_left.mpr h ] ; assumption


-- 2.1.10a
example {G : Type} [Group G] (H K : Subgroup G) : Subgroup G := {
  carrier := H.carrier ∩ K.carrier
  mul_mem' := by
    rintro x y ⟨hx, hy⟩ ⟨hx', hy'⟩
    exact ⟨H.mul_mem hx hx', K.mul_mem hy hy'⟩
  one_mem' := by
    exact ⟨H.one_mem, K.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hy⟩
    exact ⟨H.inv_mem hx, K.inv_mem hy⟩
}

-- 2.1.12 part a
example {G : Type} [Group G] (hG : IsAbelian G) (n : ℤ) : Subgroup G := {
  carrier := { a^n | a : G }
  mul_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    simp
    use a * b
    have h_weaker : ∀ m : ℕ , a ^ m * b ^ m = (a * b) ^ m := by
      intro m
      induction m with
      | zero =>
        simp
      | succ m IH =>
        rw [pow_succ (a * b), ← IH, hG a, ← mul_assoc, mul_assoc (a ^ m) _ _, mul_assoc, hG _ a]
        group
    by_cases hn : n ≥ 0
    · lift n to ℕ using hn
      have := h_weaker n
      norm_cast
      simp [this]
    · simp at hn
      obtain ⟨ m, hm ⟩ : ∃ m : ℕ, m = -n := by
        use (-n).natAbs
        grind
      obtain rfl : n = -m := by grind
      have : ∀ g : G, g ^ (-(m: ℤ)) = (g ^ m)⁻¹ := by
        intro g
        group
      simp [this]
      rw [← h_weaker m, ← mul_inv_rev, hG (b^m)]
  one_mem' := by
    use 1
    simp
  inv_mem' := by
    intro x hx
    simp at *
    obtain ⟨a, rfl⟩ := hx
    use a⁻¹
    simp
}

-- part b
example {G : Type} [Group G] (hG : IsAbelian G) (n : ℤ) : Subgroup G := {
  carrier := { a | a^n = 1 }
  mul_mem' := by
    have : ∀ x y : G, ∀ m : ℕ, (x * y)^m = x^m * y^m := by
      intro x y m
      induction m with
      | zero =>
        simp
      | succ m IH =>
        simp [pow_succ, IH]
        rw [← mul_assoc, hG _ x, ← mul_assoc, hG x]
        group

    obtain ⟨n', hn⟩ := Int.eq_nat_or_neg n
    intro a b a_1 a_2
    simp_all only [Set.mem_setOf_eq]
    cases hn with
    | inl rfl =>
      grind only [zpow_natCast, mul_one]
    | inr rfl =>
      simp_all only [zpow_neg, zpow_natCast, inv_eq_one, mul_one, inv_one]


  one_mem' := by
    simp +decide
  inv_mem' := by
    intro x a
    simp_all only [Set.mem_setOf_eq, inv_zpow', zpow_neg, inv_one]
}
