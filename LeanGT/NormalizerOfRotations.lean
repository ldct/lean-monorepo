import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

def D (n : ℕ): Subgroup (DihedralGroup n) where
  carrier := ⊤
  mul_mem' := by
    exact fun {a b} a a_1 ↦ a
  one_mem' := by trivial
  inv_mem' := fun {x} a ↦ a


-- The subgroup of rotations
def Rot (n : ℕ): Subgroup (DihedralGroup n) where
  carrier := { r i | i : ZMod n }
  mul_mem' := by
    intros a b a_is_ri b_is_ri
    cases' a_is_ri with i1 r_i1_is_a
    cases' b_is_ri with i2 r_i1_is_b
    use i1 + i2
    rw [←r_i1_is_a, ←r_i1_is_b]
    rw [r_mul_r]
  one_mem' := by
    use 0
    rfl
  inv_mem' := by
    intros x x_in_A
    cases' x_in_A with i ri_is_x
    use -i
    rw [← ri_is_x]
    rfl

-- API for `Rot n`
theorem mem_A_iff (g : DihedralGroup n) : g ∈ Rot n ↔ g ∈ { r i | i : ZMod n } := by
  rfl

-- The normalizer of the group of rotations
def N_A (n : ℕ) : Subgroup (DihedralGroup n) := (Rot n).normalizer

@[simp]
theorem inv_simp (i : ZMod n) : (sr i)⁻¹ = sr i := by
  rfl

@[simp]
theorem one_def' : r 0 = (1 : DihedralGroup n) :=
  rfl

theorem lmul {G : Type} [Group G] {a b : G} (k : G) : (a = b → a * k = b * k) := by
  exact fun a_1 ↦ congrFun (congrArg HMul.hMul a_1) k

example : ((sr 0) ∈ N_A n) := by
  have h' : N_A n = (Rot n).normalizer := by rfl
  rw [h', Subgroup.mem_normalizer_iff]
  intro g
  constructor
  rw [mem_A_iff]
  intro hg
  simp at hg
  cases' hg with i ri_is_g
  rw [← ri_is_g]
  simp
  rw [mem_A_iff]
  simp

  rw [mem_A_iff]
  simp
  intro i ri_is_sgs

  have h' := congrArg (HMul.hMul (sr 0)) ri_is_sgs
  have h'' := congrFun (congrArg HMul.hMul h') (sr 0)

  have rwl : sr 0 * (sr 0 * g * sr 0) * sr 0 = (sr 0 * sr 0) * g * (sr 0 * sr 0) := by group

  have rw2 : (sr 0 * sr 0) * g * (sr 0 * sr 0) = g := by simp

  rw [rwl, rw2] at h''

  rw [←h'']

  simp
  rw [mem_A_iff]
  simp

-- Direct proof that sr j ∈ N
example (j : ZMod n) : ((sr j) ∈ N_A n) := by
  have h' : N_A n = (Rot n).normalizer := by rfl
  rw [h', Subgroup.mem_normalizer_iff]
  intro g
  constructor
  rw [mem_A_iff]
  intro hg
  simp at hg
  cases' hg with i ri_is_g
  rw [← ri_is_g]
  simp
  rw [mem_A_iff]
  simp

  rw [mem_A_iff]
  simp
  intro i ri_is_sgs

  have h' := congrArg (HMul.hMul (sr j)) ri_is_sgs
  have h'' := congrFun (congrArg HMul.hMul h') (sr j)

  have rwl : sr j * (sr j * g * sr j) * sr j = (sr j * sr j) * g * (sr j * sr j) := by group

  have rw2 : (sr j * sr j) * g * (sr j * sr j) = g := by simp

  rw [rwl, rw2] at h''

  rw [←h'']

  simp
  rw [mem_A_iff]
  simp

theorem t1 : (Rot n).normalizer = (DihedralGroup n) := by
  sorry
-- example : N_A n = DihedralGroup n := by
--   apply le_antisymm
