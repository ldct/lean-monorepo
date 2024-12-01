import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- s*s = 1
example (n: ℕ) : (sr 0: DihedralGroup n) * (sr 0) = (r 0) := by simp

-- sr r = r^-1 sr
example (n: ℕ) : (sr 1: DihedralGroup n) * (r 1) = r (-1) * (sr 1) := by simp

example (n: ℕ) : (sr 2: DihedralGroup n) * (r 1) = r (-1) * (sr 2) := by simp

-- Let x be a reflection (i.e. x = sr k), then x acts on r by inversion.
-- x r x = r^-1
example (n k: ℕ) : (sr k: DihedralGroup n) * (r 1) * (sr k) = r (-1) := by simp

-- Various concrete subgroups of concrete dihedral groups

example : Subgroup (DihedralGroup 4) where
  carrier := {r 0}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : Subgroup (DihedralGroup 4) where
  carrier := { r 0 , sr 0 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 0, sr 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 1, sr 3 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : Subgroup (DihedralGroup 6) where
  carrier := { r 0 } ∪ { sr 0 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

-- The subgroup of even powers of r. (Note: this could be equal to all powers of r if n is odd)
example (n : ℕ): Subgroup (DihedralGroup n) where
  carrier := { r (2*i) | i : ZMod n }
  mul_mem' := by
    intros a b ha hb
    simp at ha
    simp at hb
    cases' ha with i ha
    cases' hb with j hb
    rw [← ha, ← hb]
    simp
    use i + j
    ring
  one_mem' := by
    use 0
    simp
    rfl
  inv_mem' := by
    intros x hx
    simp at hx
    cases' hx with i hi
    use -i
    rw [← hi]

    have rr : (r (2 * i))⁻¹ = r (- (2 * i)) := by
      rfl

    rw [rr]
    ring_nf

-- Example 2 in dummit and foote
def A : Subgroup (DihedralGroup 4) where
  carrier := { r i | i : ZMod 4 }
  mul_mem' := by
    intros a b
    fin_cases a <;> fin_cases b <;> decide
  one_mem' := by decide
  inv_mem' := by
    intros a
    fin_cases a <;> decide

theorem mem_f4_iff (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> decide


theorem mem_z4_iff (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  change Fin 4 at i
  exact mem_f4_iff i

theorem mem_A_iff' (g : DihedralGroup 4) : g ∈ A ↔ g ∈ { r i | i : ZMod 4 } := Iff.rfl

theorem mem_A_iff (g : DihedralGroup 4) : g ∈ A ↔ g = r 0 ∨ g = r 1 ∨ g = r 2 ∨ g = r 3:= by {
  rw [mem_A_iff']
  fin_cases g <;> decide
}

def C_A : Subgroup (DihedralGroup 4) := Subgroup.centralizer A

example (G : Type) [Group G] (H : Subgroup G) : Subgroup.centralizer H ≤ Subgroup.normalizer H := by {
  intros g g_centralizes_h
  have ginv_centralizes_h : g⁻¹ ∈ Subgroup.centralizer H := by {
    exact Subgroup.inv_mem (Subgroup.centralizer ↑H) g_centralizes_h
  }
  have conj_by_ginv' (h : G) : h ∈ H → g⁻¹ * h * g ∈ H := by {
    intro hh
    specialize ginv_centralizes_h h
    rw [←ginv_centralizes_h]
    simp
    exact hh
    exact hh
  }
  rw [Subgroup.mem_centralizer_iff] at g_centralizes_h
  rw [Subgroup.mem_normalizer_iff]
  intros h
  constructor
  intros hh
  have rw1 := g_centralizes_h h hh
  rw [← rw1]
  group
  exact hh
  intros h'
  have spec := conj_by_ginv' (g * h * g⁻¹) h'
  group at spec
  exact spec
}




-- example 2 on page 50
theorem A_le_CA : A ≤ C_A := by
  intros a ha
  intros b hb
  simp only [Subgroup.mem_carrier, SetLike.mem_coe] at hb
  rw [mem_A_iff] at ha
  rw [mem_A_iff] at hb
  cases ha <;> cases hb <;> aesop

theorem A_le_CA_carrier : A.carrier ≤ C_A.carrier := by
  exact A_le_CA


theorem ri_in_CA (i : ZMod 4) : r i ∈ C_A := by
  apply A_le_CA
  rw [mem_A_iff]
  fin_cases i <;> decide

theorem s_not_in_CA : (sr 0) ∉ C_A := by
  intro hs
  specialize hs (r 1)
  simp at hs
  have t : ((-1 : ZMod 4) = 1) -> False := by decide
  apply t
  apply hs
  rw [mem_A_iff]
  simp only [r.injEq, true_or, or_true]

example (i : ZMod 4) : (sr i ∉ C_A) := by
  by_contra rs_i_in_CA
  have r_i_inv_in_CA := ri_in_CA (-i)
  have mul := Subgroup.mul_mem C_A rs_i_in_CA r_i_inv_in_CA
  simp at mul
  apply s_not_in_CA
  exact mul

theorem A_complement_is_sr (x : DihedralGroup 4) (hx : x ∉ A) : ∃ i, x = sr i := by
  cases' x with i i
  exfalso
  have spec := mem_A_iff' (r i)
  rw [spec] at hx
  simp at hx
  use i

theorem A_le_CA' : C_A.carrier ≤ A.carrier := by
  intro x x_in_CA
  by_contra x_not_in_A
  have spec := A_complement_is_sr x x_not_in_A
  cases' spec with i x_eq_sr_i
  have r_neg_i_in_CA := ri_in_CA (-i)
  have prod_in_CA := Subgroup.mul_mem C_A x_in_CA r_neg_i_in_CA
  rw [x_eq_sr_i] at prod_in_CA
  simp at prod_in_CA
  apply s_not_in_CA
  exact prod_in_CA


theorem A_eq_CA_carrier : A.carrier = C_A.carrier := by {
  exact le_antisymm A_le_CA_carrier A_le_CA'
}

theorem A_eq_CA : A = C_A := by {
  ext a
  rw [← Subgroup.mem_carrier]
  rw [← Subgroup.mem_carrier]
  have h1 := Eq.le A_eq_CA_carrier
  have h2 := Eq.le A_eq_CA_carrier.symm
  constructor
  intro ha
  exact h1 (h2 (h1 ha))
  intro ha
  exact h2 (h1 (h2 ha))
}


example : (1 : ZMod 4) ≠ -1 := by decide
