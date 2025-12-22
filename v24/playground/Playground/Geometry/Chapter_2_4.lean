import Mathlib

def IndexedIntersection
{G} [Group G] (𝒞 : Set (Subgroup G)) : Subgroup G := {
  carrier := ⋂ (H ∈ 𝒞), H.carrier
  mul_mem' := by
    intro a b ha hb
    simp at *
    intro H hH
    specialize ha H hH
    specialize hb H hH
    exact H.mul_mem ha hb
  one_mem' := by
    rw [Set.mem_iInter]
    simp
  inv_mem' := by
    intro a ha
    rw [Set.mem_iInter] at *
    intro H hH
    specialize ha H hH
    simp at *
    intro h2
    specialize ha h2
    intro h3
    specialize ha h3
    rw [← h3] at ha
    rw [← h3]
    simpa
}

open MatrixGroups in
abbrev G := SL(2, ℤ)

def Hn (n : ℕ) : Subgroup G := CongruenceSubgroup.Gamma0 n

example : IndexedIntersection { Hn n | n ∈ Set.univ } = {g : G | g 1 0 = 0} := by
  -- To prove equality of sets, we show each set is a subset of the other.
  ext g
  simp [IndexedIntersection, Hn];
  -- If $g 1 0$ is zero, then obviously for any $i$, $(g 1 0) \mod i$ is zero.
  constructor
  · intro h
    by_contra h_nonzero
    obtain ⟨i, hi⟩ : ∃ i : ℕ, ¬(i ∣ Int.natAbs (g 1 0)) := by
      exact ⟨ Int.natAbs ( g 1 0 ) + 1, Nat.not_dvd_of_pos_of_lt ( Int.natAbs_pos.mpr h_nonzero ) ( Nat.lt_succ_self _ ) ⟩;
    specialize h i;
    rw [ ZMod.intCast_zmod_eq_zero_iff_dvd ] at h
    exact hi <| Int.natAbs_dvd_natAbs.mpr h
  · intro h
    simp [h]


abbrev ZMul := Multiplicative ℚ

def Hp (p : ℕ) [Fact (Prime p)] : Subgroup ZMul := {
  carrier := { x | x.den ≡ 0 [MOD p] }
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
}

def Closure {G} [Group G] (A : Set G) : Subgroup G :=
  IndexedIntersection { H : Subgroup G | A ⊆ H.carrier }

-- Exercise 1
example {G} [Group G] (H : Subgroup G) : H = Closure H := by
  ext x
  constructor
  · intro hx
    simp at hx
    simp [Closure, IndexedIntersection]
    intro i hi
    have hi : H ≤ i := hi
    grw [hi] at hx
    exact hx
  · intro hx
    simp [Closure, IndexedIntersection] at hx
    exact hx H (by norm_cast)

-- Exercise 2
example {G} [Group G] (A B : Set G) (hAB : A ⊆ B) : Closure A ≤ Closure B := by
  intro g hg
  simp [Closure, IndexedIntersection] at *
  grind

def Group.IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

def Subgroup.IsAbelian {G} [Group G] (H : Subgroup G) : Prop := ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

-- Exercise 3
example {G} [Group G] (H : Subgroup G) (h1 : Group.IsAbelian H) : Group.IsAbelian
    (Closure (H.carrier ∪ (Subgroup.center G).carrier)) := by
  intro x y;
  rcases x with ⟨ x, hx ⟩;
  rcases y with ⟨ y, hy ⟩;
  -- Since $x$ and $y$ are in the closure of $H \cup \text{center}(G)$, they can be written as products of elements from $H$ and $\text{center}(G)$.
  have hx_prod : ∀ x ∈ Closure (H.carrier ∪ (Subgroup.center G).carrier), ∃ (h : G), h ∈ H ∧ ∃ (c : G), c ∈ Subgroup.center G ∧ x = h * c := by
    intro x hx
    have hx_prod : x ∈ Subgroup.closure (H.carrier ∪ (Subgroup.center G).carrier) := by
      convert hx;
    refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ hx_prod;
    · rcases hx with ( hx | hx ) <;> [ exact ⟨ x, hx, 1, Subgroup.one_mem _, by simp +decide ⟩ ; exact ⟨ 1, Subgroup.one_mem _, x, hx, by simp +decide ⟩ ];
    · exact ⟨ 1, H.one_mem, 1, Subgroup.one_mem _, by simp +decide ⟩;
    · rintro x y hx hy ⟨ h₁, hh₁, c₁, hc₁, rfl ⟩ ⟨ h₂, hh₂, c₂, hc₂, rfl ⟩;
      refine' ⟨ h₁ * h₂, H.mul_mem hh₁ hh₂, c₁ * c₂, Subgroup.mul_mem _ hc₁ hc₂, _ ⟩;
      simp +decide only [← mul_assoc];
      simp +decide only [mul_assoc, Subgroup.mem_center_iff.mp hc₁ h₂];
    · rintro x hx ⟨ h, hh, c, hc, rfl ⟩;
      exact ⟨ h⁻¹, H.inv_mem hh, c⁻¹, Subgroup.inv_mem _ hc, by simp +decide [ mul_inv_rev, Subgroup.mem_center_iff.mp hc ] ⟩;
  obtain ⟨ h1, hh1, c1, hc1, rfl ⟩ := hx_prod x hx; obtain ⟨ h2, hh2, c2, hc2, rfl ⟩ := hx_prod y hy; simp_all +decide [ mul_assoc, Subgroup.mem_center_iff ] ;
  simp +decide only [← mul_assoc];
  -- Since $H$ is Abelian, we have $h1 * h2 = h2 * h1$.
  have h_comm : h1 * h2 = h2 * h1 := by
    rename_i h;
    have := h ( ⟨ h1, hh1 ⟩ : H ) ( ⟨ h2, hh2 ⟩ : H ) ; aesop;
  simp +decide only [hc2, mul_assoc, h_comm, hc1];
  simp +decide only [← mul_assoc, ← hc2]
