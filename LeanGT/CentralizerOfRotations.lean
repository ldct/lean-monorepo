import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- Generalize Example 2 in dummit and foote; the centralizer of the rotation subgroup of D_2n is itself

def A (n : ℕ): Subgroup (DihedralGroup n) where
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

theorem mem_A_iff (g : DihedralGroup n) : g ∈ A n ↔ g ∈ { r i | i : ZMod n } := by
  rfl

def C_A (n : ℕ) : Subgroup (DihedralGroup n) := Subgroup.centralizer (A n)

-- A direct proof that A centralizes itself. The proof shows that A is commutative.
theorem A_le_CA : (A n) ≤ (C_A n) := by
  intros a ha b hb
  have hb : b ∈ (A n) := hb
  rw [mem_A_iff] at ha
  rw [mem_A_iff] at hb
  cases' ha with i ri_is_a
  cases' hb with j rj_is_b
  rw [← rj_is_b]
  rw [← ri_is_a]
  simp
  exact AddCommMagma.add_comm j i

theorem A_le_CA_carrier : (A n).carrier ≤ (C_A n).carrier := by
  intros a ha
  apply A_le_CA
  exact ha

theorem ri_in_CA (i : ZMod n) : r i ∈ (C_A n) := by
  apply A_le_CA
  rw [mem_A_iff]
  simp

theorem neg_1_eq_n_minus_1 : ((-1 : ZMod n) = n-1) := by {
  simp only [CharP.cast_eq_zero, zero_sub]
}

example (a : ZMod n) (b : ZMod n) (h : a = b) : a.val = b.val := by
  exact congrArg ZMod.val h

theorem s_not_in_CA (hn : 2 < n): (sr 0) ∉ (C_A n) := by
  intro hs
  specialize hs (r 1)
  simp at hs
  have t : ((-1 : ZMod n) = 1) -> False := by {
    have : Fact (2 < n) := .mk hn
    apply ZMod.neg_one_ne_one
  }
  apply t
  apply hs
  rw [mem_A_iff]
  simp

example (i : ZMod n) (hn : 2 < n): (sr i ∉ (C_A n)) := by
  by_contra rs_i_in_CA
  have r_i_inv_in_CA := ri_in_CA (-i)
  have mul := Subgroup.mul_mem (C_A n) rs_i_in_CA r_i_inv_in_CA
  simp at mul
  exact s_not_in_CA hn mul

theorem mem_A_iff' (g : DihedralGroup n) : g ∈ A n ↔ g ∈ { r i | i : ZMod n } := Iff.rfl

theorem A_complement_is_sr (x : DihedralGroup n) (hx : x ∉ (A n)) : ∃ i, x = sr i := by
  cases' x with i i
  exfalso
  have spec := mem_A_iff' (r i)
  rw [spec] at hx
  simp at hx
  use i

theorem A_le_CA' (hn : 2 < n): (C_A n).carrier ≤ (A n).carrier := by
  intro x x_in_CA
  by_contra x_not_in_A
  have spec := A_complement_is_sr x x_not_in_A
  cases' spec with i x_eq_sr_i
  have r_neg_i_in_CA := ri_in_CA (-i)
  have prod_in_CA := Subgroup.mul_mem (C_A n) x_in_CA r_neg_i_in_CA
  rw [x_eq_sr_i] at prod_in_CA
  simp at prod_in_CA
  apply s_not_in_CA
  exact hn
  exact prod_in_CA


theorem A_eq_CA_carrier (hn : 2 < n): (A n).carrier = (C_A n).carrier := by {
  exact le_antisymm A_le_CA_carrier (A_le_CA' hn)
}

theorem A_eq_CA (hn : 2 < n) : (A n) = (C_A n) := by {
  ext a
  rw [← Subgroup.mem_carrier]
  rw [← Subgroup.mem_carrier]
  have h1 := Eq.le (A_eq_CA_carrier hn)
  have h2 := Eq.le (A_eq_CA_carrier hn).symm
  constructor
  intro ha
  exact h1 (h2 (h1 ha))
  intro ha
  exact h2 (h1 (h2 ha))
}
