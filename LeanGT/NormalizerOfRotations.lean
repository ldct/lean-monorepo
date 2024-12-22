import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

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
theorem mem_rot_iff (g : DihedralGroup n) : g ∈ Rot n ↔ g ∈ { r i | i : ZMod n } := by
  rfl

-- API for `Rot n`
theorem mem_rot_iff' (g : DihedralGroup n) : g ∈ (Rot n).carrier ↔ g ∈ { r i | i : ZMod n } := by
  rfl

-- The normalizer of the group of rotations
def N_A (n : ℕ) : Subgroup (DihedralGroup n) := (Rot n).normalizer

@[simp]
theorem inv_sr_simp (i : ZMod n) : (sr i)⁻¹ = sr i := by
  rfl

@[simp]
theorem inv_r_simp (i : ZMod n) : (r i)⁻¹ = r (-i) := by
  rfl

@[simp]
theorem one_def' : r 0 = (1 : DihedralGroup n) :=
  rfl

theorem lmul {G : Type} [Group G] {a b : G} (k : G) : (a = b → a * k = b * k) := by
  exact fun a_1 ↦ congrFun (congrArg HMul.hMul a_1) k

theorem r_in_normalizer (j : ZMod n) : ((r j) ∈ (Rot n).normalizer) := by
  have h' : (Rot n) ≤ (Rot n).normalizer := Subgroup.le_normalizer
  apply h'
  rw [mem_rot_iff]
  simp

-- Direct proof that sr j ∈ N
theorem sr_in_normalizer (j : ZMod n) : ((sr j) ∈ N_A n) := by
  have h' : N_A n = (Rot n).normalizer := by rfl
  rw [h', Subgroup.mem_normalizer_iff]
  intro g
  constructor
  rw [mem_rot_iff]
  intro hg
  simp at hg
  cases' hg with i ri_is_g
  rw [← ri_is_g]
  simp
  rw [mem_rot_iff]
  simp

  rw [mem_rot_iff]
  simp
  intro i ri_is_sgs

  have h' := congrArg (HMul.hMul (sr j)) ri_is_sgs
  have h'' := congrFun (congrArg HMul.hMul h') (sr j)

  have rwl : sr j * (sr j * g * sr j) * sr j = (sr j * sr j) * g * (sr j * sr j) := by group

  have rw2 : (sr j * sr j) * g * (sr j * sr j) = g := by simp

  rw [rwl, rw2] at h''

  rw [←h'']

  simp
  rw [mem_rot_iff]
  simp

theorem t1 : (Rot n).normalizer = ⊤ := by
  apply Subgroup.ext
  intro x
  constructor
  exact fun a ↦ trivial
  intro hx
  cases' x with i j
  exact r_in_normalizer i
  exact sr_in_normalizer j

-- DF's proof is slighty different - example 3 on p50

-- The subgroup {1, r2}
def R2 : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

#check Subgroup.center (DihedralGroup 4)

-- ex 4... too tedious...
example : (Subgroup.center (DihedralGroup 4)) = R2 := by
  have h : (Subgroup.center (DihedralGroup 4)) ≤ Subgroup.centralizer (Rot 4) := by exact?
  have h' : Subgroup.centralizer (Rot 4) = Rot 4 := by sorry
  rw [h'] at h

  have h : (Subgroup.center (DihedralGroup 4)).carrier ≤ (Rot 4).carrier := h
  simp at h
  have l : (Rot 4).carrier = { r 0, r 1, r 2, r 3} := by
    ext x
    rw [mem_rot_iff']
    simp
  sorry

-- center of DihedralGroup n

example [NeZero n] (H : (Subgroup (DihedralGroup n))) (i : ZMod n) : r 1 ∈ H → r i ∈ H := by
  intro r_in_H
  have : (r 1)^(i.val) = r i := by
    rw [r_one_pow]
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
  rw [← this]
  exact Subgroup.pow_mem H r_in_H i.val

example (i : ℤ) : i < 0 ∨ i ≥ 0 := by exact Int.lt_or_le i 0

theorem r_one_pow' (k : ℤ) : (r 1 : DihedralGroup n) ^ k = r k := by
  have := Int.lt_or_le k 0
  cases' this with neg pos
  have : ∃ p, k = -p ∧ p ≥ 0 := by
    use -k
    simp
    exact Int.le_of_lt neg
  cases' this with p hp
  cases' hp with k_is_np p_pos
  lift p to ℕ using p_pos
  rw [k_is_np]
  simp
  lift k to ℕ using pos
  simp

example (H : (Subgroup (DihedralGroup 0))) (i : ZMod 0) : r 1 ∈ H → r i ∈ H := by
  intro r_in_H
  change ℤ at i
  have : (r (1 : ZMod 0))^i = r i := by
    exact r_one_pow' i

-- a subgroup that contains r contains all powers of r
theorem r1_then_rj [NeZero n] (H : (Subgroup (DihedralGroup n))) : (r 1 ∈ H) → r i ∈ H := by
  intro r1_in_H
  have : (r 1)^(i.val) = r i := by
    rw [r_one_pow]
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
  rw [← this]
  exact Subgroup.pow_mem H r1_in_H i.val

-- a subgroup that contains r and s is the whole group
example [NeZero n] (H : (Subgroup (DihedralGroup n))) : (r 1 ∈ H) → (sr 0 ∈ H) → H = ⊤ := by
  intro r_in_H s_in_H
  ext x
  constructor
  exact fun a ↦ trivial
  intro _
  cases' x with i j
  exact r1_then_rj H r_in_H
  have : sr j = (sr 0) * (r j) := by simp
  rw [this]
  have : r j ∈ H := by exact r1_then_rj H r_in_H
  exact (Subgroup.mul_mem_cancel_right H this).mpr s_in_H


-- theorem mem_center_iff_commutes_r_rs (g : DihedralGroup n) : g ∈ Subgroup.center (DihedralGroup n) ↔
