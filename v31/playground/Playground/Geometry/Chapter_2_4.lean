import Mathlib

namespace Chapter_2_4

/-
This file formalizes the definitions, theorems and exercises from
Chapter 2.4 of Dummit and Foote (page 61).
-/

-- A preliminary definition - the indexed intersection of a family of subgroups.
def IndexedIntersection
    {G} [Group G] (𝒞 : Set (Subgroup G)) : Subgroup G where
  carrier := ⋂ (H ∈ 𝒞), H.carrier
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_iInter, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Subgroup.mem_toSubmonoid] at *
    intro H hH
    exact H.mul_mem (ha H hH) (hb H hH)
  one_mem' := by
    rw [Set.mem_iInter]
    simp
  inv_mem' := by
    intro a ha
    rw [Set.mem_iInter] at *
    intro H hH
    specialize ha H hH
    simp only [Set.mem_range, exists_prop, and_imp] at *
    intro h2
    specialize ha h2
    intro h3
    specialize ha h3
    rw [← h3] at ha
    rw [← h3]
    simpa

open MatrixGroups in
abbrev G := SL(2, ℤ)

def Hn (n : ℕ) : Subgroup G := CongruenceSubgroup.Gamma0 n

-- The intersection of all congruence subgroups Γ₀(n) consists of matrices
-- whose (1,0) entry is zero.
example : IndexedIntersection { Hn n | n ∈ Set.univ } = {g : G | g 1 0 = 0} := by
  ext g
  simp [IndexedIntersection, Hn]
  constructor
  · -- Forward: if g is in every Γ₀(n), then g 1 0 = 0.
    -- If g 1 0 ≠ 0, pick n = |g 1 0| + 1, which cannot divide |g 1 0|.
    intro h
    by_contra h_nonzero
    obtain ⟨i, hi⟩ : ∃ i : ℕ, ¬(i ∣ Int.natAbs (g 1 0)) :=
      ⟨Int.natAbs (g 1 0) + 1,
        Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr h_nonzero) (Nat.lt_succ_self _)⟩
    specialize h i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact hi <| Int.natAbs_dvd_natAbs.mpr h
  · -- Backward: if g 1 0 = 0, then (g 1 0) mod n = 0 for all n.
    intro h
    simp [h]

abbrev ZMul := Multiplicative ℚ

def Hp (p : ℕ) [Fact (Prime p)] : Subgroup ZMul where
  carrier := { x | x.den ≡ 0 [MOD p] }
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry

def Closure {G} [Group G] (A : Set G) : Subgroup G :=
  IndexedIntersection { H : Subgroup G | A ⊆ H.carrier }

-- Exercise 1: A subgroup equals the closure of its underlying set.
example {G} [Group G] (H : Subgroup G) : H = Closure H := by
  ext x
  constructor
  · -- x ∈ H implies x is in every subgroup containing H
    intro hx
    simp at hx
    simp [Closure, IndexedIntersection]
    intro i hi
    have hi : H ≤ i := hi
    grw [hi] at hx
    exact hx
  · -- x in the closure of H is in particular in H itself
    intro hx
    simp [Closure, IndexedIntersection] at hx
    exact hx H (by norm_cast)

-- Exercise 2: Closure is monotone — if A ⊆ B then ⟨A⟩ ≤ ⟨B⟩.
example {G} [Group G] (A B : Set G) (hAB : A ⊆ B) : Closure A ≤ Closure B := by
  intro g hg
  simp [Closure, IndexedIntersection] at *
  grind

def Group.IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

def Subgroup.IsAbelian {G} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

-- Exercise 3: If H is abelian, then the closure of H ∪ Z(G) is also abelian.
-- Key idea: every element of ⟨H ∪ Z(G)⟩ can be written as h * c with h ∈ H, c ∈ Z(G),
-- and commutativity follows from H being abelian and Z(G) commuting with everything.
example {G} [Group G] (H : Subgroup G) (h1 : Group.IsAbelian H) : Group.IsAbelian
    (Closure (H.carrier ∪ (Subgroup.center G).carrier)) := by
  intro x y
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  -- Decomposition lemma: every element of the closure can be written as h * c
  -- with h ∈ H and c ∈ Z(G).
  have hx_prod :
      ∀ x ∈ Closure (H.carrier ∪ (Subgroup.center G).carrier),
      ∃ (h : G), h ∈ H ∧ ∃ (c : G), c ∈ Subgroup.center G ∧ x = h * c := by
    intro x hx
    have hx_prod : x ∈ Subgroup.closure (H.carrier ∪ (Subgroup.center G).carrier) := by
      convert hx
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ ?_ ?_ hx_prod
    · -- Base case: elements from H or Z(G)
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, Subgroup.one_mem _, by simp +decide⟩
      · exact ⟨1, Subgroup.one_mem _, x, hx, by simp +decide⟩
    · -- Identity element
      exact ⟨1, H.one_mem, 1, Subgroup.one_mem _, by simp +decide⟩
    · -- Multiplication: (h₁c₁)(h₂c₂) = (h₁h₂)(c₁c₂) using centrality of c₁
      rintro x y hx hy ⟨h₁, hh₁, c₁, hc₁, rfl⟩ ⟨h₂, hh₂, c₂, hc₂, rfl⟩
      refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, c₁ * c₂, Subgroup.mul_mem _ hc₁ hc₂, ?_⟩
      -- Rearrange h₁ * c₁ * (h₂ * c₂) = (h₁ * h₂) * (c₁ * c₂) using c₁h₂ = h₂c₁
      simp +decide only [← mul_assoc]
      simp +decide only [mul_assoc, Subgroup.mem_center_iff.mp hc₁ h₂]
    · -- Inverse: (hc)⁻¹ = h⁻¹c⁻¹
      rintro x hx ⟨h, hh, c, hc, rfl⟩
      exact ⟨h⁻¹, H.inv_mem hh, c⁻¹, Subgroup.inv_mem _ hc,
        by simp +decide [mul_inv_rev, Subgroup.mem_center_iff.mp hc]⟩
  -- Decompose x = hg1 * cg1 and y = hg2 * cg2
  obtain ⟨hg1, hhg1, cg1, hcg1, rfl⟩ := hx_prod x hx
  obtain ⟨hg2, hhg2, cg2, hcg2, rfl⟩ := hx_prod y hy
  -- Since H is abelian, hg1 * hg2 = hg2 * hg1
  have h_comm : hg1 * hg2 = hg2 * hg1 := by
    have := h1 (⟨hg1, hhg1⟩ : H) (⟨hg2, hhg2⟩ : H)
    aesop
  -- Use center commutativity and H-commutativity to conclude
  simp_all +decide [Subgroup.mem_center_iff]
  apply Subtype.ext
  change cg1 * hg1 * (cg2 * hg2) = cg2 * hg2 * (cg1 * hg1)
  have := hcg1 hg2; have := hcg1 cg2; have := hcg2 hg1; have := hcg2 cg1
  have := hcg1 (hg2 * cg2); have := hcg2 (hg1 * cg1)
  grind

end Chapter_2_4
