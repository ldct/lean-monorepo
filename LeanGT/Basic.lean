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

-- The subgroup of even powers of r. (Note: this could be equal to all powers of r if n is odd)
example (n : ℕ): Subgroup (DihedralGroup n) where
  carrier := { r (2*i) | i : ZMod n }
  mul_mem' := by
    intros a b ha hb
    cases' ha with i ha
    cases' hb with j hb
    rw [← ha, ← hb]
    use i + j
    simp
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

-- The image of a homomorphism is a subgroup

example (G H: Type) [Group G] [Group H] (φ : G →* H): Subgroup H where
  carrier := { φ g | g : G }
  mul_mem' := by
    intros a b a_in_G b_in_G
    simp at a_in_G
    simp at b_in_G
    cases' a_in_G with a' phi_a'_is_a
    cases' b_in_G with b' phi_b'_is_b
    simp
    use a' * b'
    have h : φ (a' * b') = (φ a') * φ b' := by
      exact MonoidHom.map_mul φ a' b'
    rw [h, phi_a'_is_a, phi_b'_is_b]
  one_mem' := by
    simp
    use 1
    exact MonoidHom.map_one φ
  inv_mem' := by
    intros g hg
    simp at hg
    cases' hg with g' phi_g'_is_g
    simp
    use g'⁻¹
    simp
    exact phi_g'_is_g

example : (1 : ZMod 4) ≠ -1 := by decide
