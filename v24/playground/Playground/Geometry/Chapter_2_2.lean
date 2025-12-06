import Mathlib
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- Definition, p49. Define C_G(A), the centralizer of A in G, as a subgroup of G.
def MyCentralizer {G} [Group G] (A : Set G) : Subgroup G := {
  carrier := { g : G | ∀ a ∈ A, g * a * g⁻¹ = a }
  mul_mem' := by
    intro x y hx hy
    simp at *
    intro a ha
    nth_rw 2 [← hx a ha]
    nth_rw 2 [← hy a ha]
    group
  one_mem' := by
    intro a ha
    group
  inv_mem' := by
    intro x hx a ha
    simp at *
    nth_rw 1 [← hx a ha]
    group
}

-- Definition, p50. Define Z(G), the center of G, as a subgroup of G.
def MyCenter (G) [Group G] : Subgroup G := {
  carrier := { g : G | ∀ a : G, g * a * g⁻¹ = a }
  mul_mem' := by
    intro x y hx hy
    simp at *
    intro a
    nth_rw 2 [← hx a, ← hy a]
    group
  one_mem' := by
    intro a
    group
  inv_mem' := by
    intro x hx a
    simp at *
    nth_rw 1 [← hx a]
    group
}

-- Note that Z(G) = C_G(G).
example {G} [Group G] : (MyCenter G) = (MyCentralizer ⊤) := by
  simp [MyCenter, MyCentralizer]

-- Definition, p50. While the book defines gAg⁻¹, we generalize it a bit to hAg.
def MyMap {G} [Group G] (h : G) (A : Set G) (g : G) : Set G :=
  { h * a * g | a ∈ A }

-- An auxiliary definition. The normalizer of A will be all g such that `Normalizes g A` holds.
def Normalizes {G} [Group G] (g : G) (A : Set G) : Prop := MyMap g A g⁻¹ = A

theorem inv_normalizes {G} [Group G]
  {A : Set G} {g : G} (hg : Normalizes g A)
: Normalizes g⁻¹ A := by
  have h_inv : ∀ a ∈ A, g⁻¹ * a * g ∈ A := by
    have h_inv : ∀ a ∈ A, ∃ b ∈ A, g * b * g⁻¹ = a := by
      intro a a1
      simp [Normalizes, MyMap, Set.ext_iff] at hg
      rwa [← hg a] at a1
    intro a ha
    obtain ⟨ b, hb, hab ⟩ := h_inv a ha
    simp [← hab, mul_assoc, hb]
  ext x
  constructor
  · intro hx
    simp_all [ mul_assoc ]
    cases' hx with w h
    obtain ⟨left, right⟩ := h
    subst right
    simpa only [ mul_assoc ] using h_inv _ left;
  · intro hx
    exact ⟨
    g * x * g⁻¹,
    by simpa [ mul_assoc ] using hg.subset ( Set.mem_image_of_mem _ hx ),
    by group ⟩

theorem test1 {G} [Group G] {A : Set G} {g : G} (h : Normalizes g A) (a : G) (ha : a ∈ A)
: g * a * g⁻¹ ∈ A := by
  simp [Normalizes, MyMap] at h
  rw [← h]
  simp [ha]

theorem test2 {G} [Group G] {A : Set G} {g : G} (h : Normalizes g A) (a : G) (ha : a ∈ A)
: g⁻¹ * a * g ∈ A := by
  nth_rw 2 [show g = g⁻¹⁻¹ by group]
  apply test1
  · exact inv_normalizes h
  · exact ha

theorem mul_normalizes
  {G} [Group G] {A : Set G} {g₁ g₂ : G} (h1 : Normalizes g₁ A) (h2 : Normalizes g₂ A)
: Normalizes (g₁ * g₂) A := by
  simp [Normalizes, MyMap]
  ext a
  constructor
  · rintro ⟨ b, hb1, hb2 ⟩
    rw [← hb2]
    rw [show g₁ * g₂ * b * (g₂⁻¹ * g₁⁻¹) = g₁ * (g₂ * b * g₂⁻¹) * g₁⁻¹ by group]
    apply test1 h1
    apply test1 h2
    exact hb1
  intro ha
  simp
  use (g₂⁻¹ * g₁⁻¹ * a * g₁ * g₂)
  constructor
  · rw [show g₂⁻¹ * g₁⁻¹ * a * g₁ * g₂ = g₂⁻¹ * (g₁⁻¹ * a * g₁) * g₂ by group]
    apply test2 h2
    apply test2 h1
    exact ha
  · group

-- Definition, p50. Define N(A), the normalizer of A in G, as a subgroup of G.
def MyNormalizer {G} [Group G] (A : Set G) : Subgroup G := {
  carrier := { g : G | Normalizes g A }
  mul_mem' := by
    intro x y hx hy
    exact mul_normalizes hx hy
  one_mem' := by
    simp [Normalizes, MyMap]
  inv_mem' := by
    intro x hx
    simp_all
    exact inv_normalizes hx
}

-- Example 1 (page 50)
example {G} [CommGroup G] : Subgroup.center G = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro g
  exact CommGroup.mul_comm g x

-- The subgroup of rotations
def Rot (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := { r i | i : ZMod n }
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

theorem mem_rot_iff (n : ℕ) (g : DihedralGroup n) : g ∈ Rot n ↔ g ∈ { r i | i : ZMod n } := by
  rfl

theorem mem_rot_iff'' (n : ℕ) (g : DihedralGroup n)
: g ∈ (Rot n) ↔ ∃ i : ZMod n, g = r i := by
  constructor <;> rintro ⟨i, rfl⟩ <;> simp [Rot]

theorem nmem_rot_iff (n : ℕ) (g : DihedralGroup n)
: g ∉ Rot n ↔ ∃ i : ZMod n, g = sr i := by
  match g with
  | r _ => simp [mem_rot_iff'']
  | sr _ => simp [Rot]

example {G} [Group G] (H : Subgroup G) (g : H) (n : ℕ)
: g^n = g^n := by
  rfl

example (n : ℕ) : IsCyclic (Rot n) := ⟨ ⟨r 1, by use 1⟩, by
  rintro ⟨x, ⟨i, rfl⟩⟩
  use i.valMinAbs
  dsimp
  rw [← SetLike.coe_eq_coe]
  rw [SubgroupClass.coe_zpow, r_zpow, ZMod.coe_valMinAbs, one_mul]
⟩

theorem inv_r_simp (n : ℕ) (i : ZMod n) : (r i)⁻¹ = r (-i) := by
  rfl

theorem r_one_pow'' (n : ℕ) (k : ℤ) : (r 1 : DihedralGroup n) ^ k = r k := by exact r_one_zpow k

-- The normalizer of the group of rotations
def N_A (n : ℕ) : Subgroup (DihedralGroup n) := (Rot n).normalizer

-- The next few theorems generalize example 2 (page 50)

theorem rot_le_centralizer (n : ℕ) : Rot n ≤ Subgroup.centralizer (Rot n) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  simp at hg
  rw [mem_rot_iff''] at hx hg
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hg
  simp
  grind

theorem s_nin_centralizer (n : ℕ) [Fact (2 < n)]
: (sr 0 : DihedralGroup n) ∉ Subgroup.centralizer (Rot n) := by
  intro h
  rw [Subgroup.mem_centralizer_iff] at h
  specialize h (r 1) (by use 1)
  simp at h
  exact (ZMod.neg_one_ne_one) h

theorem sri_nin_centralizer (n : ℕ) [Fact (2 < n)] (i : ZMod n)
: (sr i : DihedralGroup n) ∉ Subgroup.centralizer (Rot n) := by
  intro h
  have h' : r (-i) ∈ Subgroup.centralizer (Rot n) := by
    grw [← rot_le_centralizer]
    simp [Rot]
  have := Subgroup.mul_mem _ h h'
  simp_all [s_nin_centralizer]

theorem centralizer_le_rot (n : ℕ) [Fact (2 < n)] : Subgroup.centralizer (Rot n) ≤ Rot n := by
  intro x hx
  by_contra h
  rw [nmem_rot_iff] at h
  obtain ⟨j, rfl⟩ := h
  exact (sri_nin_centralizer n j) hx

theorem centralizer_eq_rot (n : ℕ) [Fact (2 < n)] : Subgroup.centralizer (Rot n) = Rot n := by
  have h1 := rot_le_centralizer n
  have h2 := centralizer_le_rot n
  order

-- Example 2
theorem example_2 : Subgroup.centralizer (Rot 4) = Rot 4 := by
  have h : Fact (2 < 4) := by decide
  exact centralizer_eq_rot 4

-- The next few theorems generalize example 3 (page 50), which states:
-- Let G = D_8 and A = {1, r, r^2, r^3}. We show that N(A) = D_8.
-- We generalize this to any dihedral group: N(Rot n) = D_n.
-- In fact, since Rot n is an index-2 subgroup, it is normal in D_n

theorem r1_then_rj (n : ℕ) (i : ZMod n) (H : (Subgroup (DihedralGroup n)))
: (r 1 ∈ H) → r i ∈ H := by
  have h_closure (i : ℤ) (hi : DihedralGroup.r 1 ∈ H): DihedralGroup.r i ∈ H := by
    have := H.zpow_mem hi i
    simp_all only [r_zpow, one_mul]
  cases n
  · intro a
    simp_all only [forall_const]
    apply h_closure
  · convert h_closure i.val;
    simp_all

-- a subgroup that contains r and s is the whole group
theorem top_of_r_mem_of_s_mem {n : ℕ} {H : Subgroup (DihedralGroup n)}
(r_mem : r 1 ∈ H) (s_mem : sr 0 ∈ H)
: H = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  cases x with
  | r i => exact r1_then_rj n i H r_mem
  | sr j =>
    rw [show sr j = (sr 0) * (r j) by simp]
    apply Subgroup.mul_mem
    · exact s_mem
    · exact r1_then_rj _ _ _ r_mem

theorem r_in_normalizer (n : ℕ) (j : ZMod n) : ((r j) ∈ (Rot n).normalizer) := by
  have h' : (Rot n) ≤ (Rot n).normalizer := Subgroup.le_normalizer
  apply h'
  rw [mem_rot_iff'']
  simp

theorem s_in_normalizer (n : ℕ) : ((sr 0) ∈ N_A n) := by
  unfold N_A
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rw [mem_rot_iff'']
    rintro ⟨i, rfl⟩
    simp
    rw [mem_rot_iff'']
    simp

  rw [mem_rot_iff]
  simp
  intro i ri_is_sgs

  have h' := congrArg (HMul.hMul (sr 0)) ri_is_sgs
  have h'' := congrFun (congrArg HMul.hMul h') (sr 0)

  have : g = r (-i) := by
    have : (sr 0 : DihedralGroup n) * sr 0 = 1 := by grind [sr_mul_sr, sub_self, r_zero]
    simp only [mul_assoc, this] at h''
    simp only [← mul_assoc, this] at h''
    simp at h''
    simp_all

  simp [this, mem_rot_iff]


-- Generalization of example 3
theorem t1' (n : ℕ)
: (Rot n).normalizer = ⊤ :=
  top_of_r_mem_of_s_mem (r_in_normalizer _ _) (s_in_normalizer _)

-- Example 3
example : (Rot 4).normalizer = ⊤ := t1' 4

-- The subgroup {1, r2}
def R2 : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

-- example 4 on p50
example : (Subgroup.center (DihedralGroup 4)) = R2 := by

  have h_fact : Fact (2 < 4) := by decide
  have h1 : (Subgroup.center (DihedralGroup 4)) ≤ Subgroup.centralizer (Rot 4) := by
    apply Subgroup.center_le_centralizer
  rw [example_2] at h1

  have h2 : r 1 ∉ Subgroup.center (DihedralGroup 4) := by
    intro h
    rw [Subgroup.mem_center_iff] at h
    specialize h (sr 0)
    simp at h
    exact @ZMod.neg_one_ne_one 4 (by decide) (Eq.symm h)
  have h3 : r 3 ∉ Subgroup.center (DihedralGroup 4) := by
    intro h
    rw [Subgroup.mem_center_iff] at h
    specialize h (sr 3)
    simp at h
    norm_num at h
    exact @ZMod.neg_one_ne_one 4 (by decide) (by grind)

  have h4 : Subgroup.center (DihedralGroup 4) ≤ R2 := by
    intro g hg
    specialize h1 hg
    obtain ⟨ i, rfl ⟩ := h1
    fin_cases i <;> simp_all [R2]

  have h5 : R2 ≤ Subgroup.center (DihedralGroup 4) := by
    intro g hg
    simp [R2] at hg
    obtain rfl | rfl := hg
    · simp
    rw [Subgroup.mem_center_iff]
    intro g
    match g with
    | r i =>
      grind [r_mul_r, r.injEq]
    | sr j =>
      grind [sr_mul_r, r_mul_sr, sr.injEq]

  order

abbrev S3 := Equiv.Perm (Fin 3)

theorem card_S3 : Nat.card S3 = 6 := by
  simp [S3]
  rfl

-- The subgroup {1, (1, 2)}
def A : Subgroup S3 where
  carrier := { 1, c[0, 1] }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

theorem card_A : Nat.card A = 2 := by
  simp [A]
  decide

theorem A_le_centralizer : A ≤ Subgroup.centralizer A := by
  intro g hg
  simp [A] at hg
  rw [Subgroup.mem_centralizer_iff]
  simp [A]
  grind [Fin.isValue, mul_one, one_mul]

example {G} [Group G] (J K : Subgroup G) (h : J ≤ K) : Nat.card J ∣ Nat.card K := by
  exact Subgroup.card_dvd_of_le h

theorem card_dvd_6 : Nat.card (Subgroup.centralizer (A : Set S3)) ∣ 6 := by
  rw [← card_S3]
  apply Subgroup.card_subgroup_dvd_card

theorem two_dvd_card : 2 ∣ Nat.card (Subgroup.centralizer (A : Set S3)) := by
  rw [← card_A]
  have := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (A : Set S3))
  apply Subgroup.card_dvd_of_le
  exact A_le_centralizer

theorem two_or_six (x : ℕ) (h : x ∣ 6) (h2 : 2 ∣ x) : x = 2 ∨ x = 6 := by
  have h_divisors : x ∈ Nat.divisors 6 := by
    simp [Nat.mem_divisors, h]
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by rfl] at h_divisors
  grind

theorem card_eq_2_or_6
: (Nat.card (Subgroup.centralizer (A : Set S3))) = 2 ∨
  (Nat.card (Subgroup.centralizer (A : Set S3))) = 6 := by
  apply two_or_six
  · exact card_dvd_6
  · exact two_dvd_card

theorem nc
: ¬ (∀ h ∈ A, h * (c[0, 1, 2]) = (c[0, 1, 2]) * h) := by
  by_contra h
  specialize h (c[0, 1]) (by simp [A])
  simp at h
  have : (Equiv.swap (1 : Fin 3) 2) 0 = (Equiv.swap 1 2) 0 := by rfl
  conv at this =>
    lhs
    rw [h]
  rw [h] at this
  simp +decide at this


theorem card_eq_2
: (Nat.card (Subgroup.centralizer (A : Set S3))) = 2 := by
  obtain h | h := card_eq_2_or_6
  · exact h
  have : Subgroup.centralizer (A : Set S3) = ⊤ := by
    rwa [← Subgroup.card_eq_iff_eq_top, card_S3]
  have h1 : c[0, 1, 2] ∈ Subgroup.centralizer (A : Set S3) := by
    rw [this]
    simp
  rw [Subgroup.mem_centralizer_iff] at h1
  simp at h1
  exfalso
  exact nc h1

theorem test {G} [Group G] {H K : Subgroup G} [Finite H] [Finite K]
  (h1 : H ≤ K) (h2 : Nat.card H = Nat.card K)
: K = H := by
  have h_eq : H = K := by
    have h_card : Nat.card H = Nat.card K := h2
    have h_sub : H ≤ K := h1
    have h_eq : Set.ncard (H : Set G) = Set.ncard (K : Set G) := by
      convert h_card using 1;
    exact SetLike.ext' ( Set.eq_of_subset_of_ncard_le h_sub h_eq.ge );
  exact Eq.symm h_eq

theorem centralizer_eq_A : Subgroup.centralizer A = A := by
  have h1 := card_eq_2
  have h2 := card_A
  apply test
  · exact A_le_centralizer
  · grind

theorem center_le_A : Subgroup.center S3 ≤ A := by
  rw [← centralizer_eq_A]
  apply Subgroup.center_le_centralizer

theorem center_eq_bottom : Subgroup.center S3 = ⊥ := by
  ext g
  constructor
  · intro h
    have : g ∈ A := by
      grw [center_le_A] at h
      exact h
    obtain rfl | rfl := this <;> simp_all +decide
  · rintro rfl
    simp

theorem test3 (G : Type) [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H.normalizer)
: H.carrier = { g * h * g⁻¹ | h ∈ H.carrier } := by
  ext x
  simp
  constructor
  · intro hx
    use g⁻¹ * x * g
    have := hg ( g⁻¹ * x * g )
    grind [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  · intro a
    obtain ⟨w, ⟨ left, rfl ⟩⟩ := a
    have := hg w
    grind [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem centralizer_le_normalizer {G} [Group G] (H : Subgroup G) : Subgroup.centralizer H ≤ Subgroup.normalizer H := by {
  rintro g g_centralizes_H
  have ginv_centralizes_h : g⁻¹ ∈ Subgroup.centralizer H := by {
    simp only [Subgroup.inv_mem_iff, g_centralizes_H]
  }
  intro h
  constructor
  intro h_in_H
  rw [←(g_centralizes_H h h_in_H), mul_inv_cancel_right]
  exact h_in_H
  have conjAct_by_inv (h : G) (h_in_H : h ∈ H): g⁻¹ * h * g ∈ H := by {
    rw [←(ginv_centralizes_h h h_in_H), inv_mul_cancel_right]
    exact h_in_H
  }
  intro g_conjAct_h_in_H
  have := conjAct_by_inv (g * h * g⁻¹) g_conjAct_h_in_H
  group at this
  exact this
}

example : Subgroup.normalizer A = A := by
  ext s
  constructor
  · intro h
    have := test3 S3 A s h
    rw [show A.carrier =  { 1, c[0, 1] } by rfl] at this
    simp at this
    have := Eq.subset this
    specialize this (show Equiv.swap 0 1 ∈ _ by decide)
    simp +decide at this
    rw [← centralizer_eq_A, Subgroup.mem_centralizer_iff]
    simp [A]
    nth_rw 1 [← this]
    group

  intro h
  simp [A] at h
  obtain rfl | rfl := h
  · exact Subgroup.one_mem A.normalizer
  · grw [← centralizer_le_normalizer, centralizer_eq_A]
    simp [A]

-- Exercise 1
example {G} [Group G] (A : Set G)
: Subgroup.centralizer A = {g | ∀ a ∈ A, g⁻¹ * a * g = a}
:= by
  ext g
  simp
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro a b c
    rw [mul_assoc, a b c]
    group

  · intro h a b
    nth_rw 2 [← (h a b)]
    group


-- Exercise 2
example {G} [Group G]
: Subgroup.centralizer ((Subgroup.center G).carrier) = ⊤ := by
  ext g
  constructor
  · intro h
    trivial
  · intro _
    rw [Subgroup.mem_centralizer_iff]
    simp only [Subgroup.mem_carrier]
    simp_all [Subgroup.mem_center_iff]

-- Exercise 3
example {G} [Group G] (A B : Set G) (h : A ≤ B)
: Subgroup.centralizer B ≤ Subgroup.centralizer A := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at *
  intro a ha
  exact hg a (h ha)

-- Exercise 6a part 1. This is available in Mathlib as Subgroup.le_normalizer.
example {G} [Group G] (H : Subgroup G)
: H ≤ Subgroup.normalizer H := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · grind [Subgroup.mul_mem, Subgroup.inv_mem_iff]
  intro h1
  rw [show h = g * (g⁻¹ * h * g) * g⁻¹ by group]
  grind [Subgroup.mul_mem, Subgroup.inv_mem_iff]

def IsAbelianSubgroup {G} [Group G] (H : Subgroup G) : Prop := ∀ x ∈ H, (∀ y ∈ H, x * y = y * x)

-- Exercise 6b
example {G} [Group G] (H : Subgroup G)
: H ≤ Subgroup.centralizer H ↔ IsAbelianSubgroup H := by
  constructor
  · intro h
    intro x hx y hy
    exact h hy x hx
  · intro h
    intro x hx y hy
    exact h y hy x hx



def MySubgroupNormalizer {G} [Group G] (H : Subgroup G) (A : Set G)
: Set G :=
  { h ∈ H | MyMap h A h⁻¹ = A }

-- Exercise 9
example {G} [Group G] (H : Subgroup G) (A : Set G)
: MySubgroupNormalizer H A = (Subgroup.setNormalizer A) ⊓ H := by
  simp
  ext g
  simp [MySubgroupNormalizer, Subgroup.setNormalizer, MyMap]

  constructor
  · rintro ⟨ h1, h2 ⟩
    simp [h1]
    intro n
    nth_rw 2 [← h2]
    simp

  rintro ⟨ h1, h2 ⟩
  simp [h2]
  ext n
  constructor
  · intro h3
    simp at h3
    obtain ⟨ a, h3, h4 ⟩ := h3
    rw [← h4]
    rw [← h1 a]
    exact h3
  intro h3
  simp
  use (g⁻¹ * n * g)
  constructor
  · rw [h1]
    group
    exact h3
  · group
