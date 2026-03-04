import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs


namespace CentralizersAndNormalizers

variable {G : Type*} [Group G]

theorem centralizer_le_normalizer [Group G] (H : Subgroup G) : Subgroup.centralizer H ≤ Subgroup.normalizer H := by {
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


-- D&F pg 52, q2.1, proof via Mathlib
example [Group G] : Subgroup.centralizer (Subgroup.center G).carrier = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset]
  exact fun ⦃a⦄ a ↦ a

-- D&F pg 52, q2.1, manual proof
theorem x [Group G] : Subgroup.centralizer (Subgroup.center G) = (⊤ : Subgroup G) := by
  rw [eq_top_iff] -- rewrite as ⊤ ≤ ...
  intro g _ h h_in_center
  exact h_in_center.comm g

-- D&F pg 52, q2.2, proof via Mathlib
example [Group G] : Subgroup.normalizer (Subgroup.center G) = ⊤ := by
  sorry -- TODO: fix for v4.24 (Subgroup.le_normalizer_of_normal API changed)

-- D&F pg 52, q2.2, direct proof
example [Group G] : Subgroup.normalizer (Subgroup.center G) = ⊤ := by
  rw [eq_top_iff]
  rw [←x]
  exact centralizer_le_normalizer (Subgroup.center G)

-- D&F pg 52, q3, proof via Mathlib
example [Group G] (A B : Set G) (A_le_B : A ≤ B) : Subgroup.centralizer (B) ≤ Subgroup.centralizer A := by
  exact Subgroup.centralizer_le A_le_B

-- D&F pg 52, q6a, direct proof
example [Group G] (H : Subgroup G) : H ≤ Subgroup.normalizer H := by
  intro x xH n
  rw [H.mul_mem_cancel_right (H.inv_mem xH)]
  rw [H.mul_mem_cancel_left xH]

-- 6b, proof by mathlib
example [Group G] (H : Subgroup G) : H ≤ Subgroup.centralizer H ↔ IsMulCommutative H := by
  exact Subgroup.le_centralizer_iff_isMulCommutative

def evens := { i : ℕ | i.isPowerOfTwo }

open Pointwise

/-- 9
The proposed definition is
N_H(A) := { h ∈ H | hAh⁻¹ = A }
this has type `Set H`. It's probably better to define it as
N_H(A) := { h ∈ G | h ∈ H, hAh⁻¹ = A }
now it has type `Set H` and the statement is obvious
-/
def asSubgroup [Group G]  (H : Subgroup G) (A : Set G) := H ⊓ Subgroup.setNormalizer A

example (H : Subgroup G) (A : Set G) (g h : G) : g ∈ (asSubgroup H A) ↔ g ∈ H ∧ ∀ a, a ∈ A ↔ h * a * h⁻¹ ∈ A := by
  sorry

-- 10 informal proof: if g fixes H then it sends 1 to 1 and g to g so it centralizes H

-- 14


end CentralizersAndNormalizers