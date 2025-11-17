import Mathlib
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

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

theorem mem_rot_iff' (n : ℕ) (g : DihedralGroup n)
: g ∈ (Rot n).carrier ↔ g ∈ { r i | i : ZMod n } := by
  rfl

theorem mem_rot_iff'' (n : ℕ) (g : DihedralGroup n)
: g ∈ (Rot n) ↔ ∃ i : ZMod n, g = r i := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := h
    simp
  · rintro ⟨i, rfl⟩
    unfold Rot
    simp

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

#check Subgroup.centralizer

example {G} [Group G] (J K: Subgroup G) (h : J ≤ K) : Nat.card J ∣ Nat.card K := by
  exact Subgroup.card_dvd_of_le h

theorem card_dvd_6 : Nat.card (Subgroup.centralizer (A : Set S3)) ∣ 6 := by
  rw [← card_S3]
  apply Subgroup.card_subgroup_dvd_card

theorem two_dvd_card : 2 ∣ Nat.card (Subgroup.centralizer (A : Set S3)) := by
  rw [← card_A]
  have := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (A : Set S3))
  apply Subgroup.card_dvd_of_le
  exact A_le_centralizer

example (x : ℕ) (h : x ∣ 6) (h2 : 2 ∣ x) : x = 2 ∨ x = 6 := by
  have h_divisors : x ∈ Nat.divisors 6 := by
    simp [Nat.mem_divisors, h]
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by rfl] at h_divisors
  grind
