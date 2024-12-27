import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

example : (IsAddCyclic ℤ) := ⟨ 1, by
  intro x
  use x
  simp
⟩

example : (IsAddCyclic ℤ) := ⟨ -1, by
  intro x
  use -x
  simp
⟩

namespace DihedralGroup

-- The subgroup of rotations
def Rot (n : ℕ): Subgroup (DihedralGroup n) where
  carrier := { r i | i : ZMod n }
  mul_mem' := by
    intro a b ⟨i1, r_i1_is_a⟩ ⟨i2, r_i1_is_b⟩
    use i1 + i2
    rw [←r_i1_is_a, ←r_i1_is_b]
    rw [r_mul_r]
  one_mem' := by
    use 0
    rfl
  inv_mem' := by
    intro x ⟨i, ri_is_x⟩
    use -i
    rw [← ri_is_x]
    rfl

theorem test [Group G] (a b : G) (a_eq_b : a = b) :  a⁻¹ = b⁻¹ := by
  exact congrArg Inv.inv a_eq_b

theorem t [Group G] (h g : G) : h⁻¹ = g⁻¹ → h = g  := by
  intro x
  have := test h⁻¹ g⁻¹ x
  simp at this
  exact this

theorem inv_r_simp (i : ZMod n) : (r i)⁻¹ = r (-i) := by
  rfl

theorem r_one_pow' (k : ℤ) : (r 1 : DihedralGroup n) ^ k = r k := by
  have : k ≥ 0 ∨ k < 0 := by exact le_or_lt 0 k
  cases' this with pos neg
  lift k to ℕ using pos
  simp
  suffices : ((r (1: ZMod n)) ^ k)⁻¹ = (r k)⁻¹
  have := test _ _ this
  simp at this
  exact this
  let l := -k
  have k_eq_nl : k = -l := by exact Int.eq_neg_comm.mp rfl
  have l_pos : l ≥ 0 := by linarith
  rw [k_eq_nl]
  have : ∃ l' : ℤ, l' = l := by use l
  cases' this with l' lp_eq_l
  have : l' ≥ 0 := by
    exact?
  lift l' to ℕ using this
  simp
  rw [←lp_eq_l]
  simp [inv_r_simp]

example (n : ℕ) : IsCyclic (Rot n) := ⟨ ⟨r 1, by use 1⟩, by
  intro ⟨x, ⟨i, hi⟩⟩
  use i.valMinAbs
  simp
  refine SetLike.coe_eq_coe.mp ?_
  simp
  rw [r_one_pow']
  rw [← hi]
  simp
⟩

example : IsCyclic ((ZMod 2) × (ZMod 3)) := by
  use (1, 1)
  refine Function.HasRightInverse.surjective ?_

  sorry
