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


theorem inv_r_simp (i : ZMod n) : (r i)⁻¹ = r (-i) := by
  rfl

theorem test [Group G] (a b : G) (a_eq_b : a = b) :  a⁻¹ = b⁻¹ := by
  exact congrArg Inv.inv a_eq_b

theorem r_one_pow'' (k : ℤ) : (r 1 : DihedralGroup n) ^ k = r k := by
  have d := le_or_lt 0 k
  cases' d with pos neg
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
  rw [r_one_pow'']
  rw [← hi]
  simp
⟩
