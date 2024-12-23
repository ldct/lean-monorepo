import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- The subgroups of Dih6 - https://people.maths.bris.ac.uk/~matyd/GroupNames/1/D6.html

-- ⊥

def bot : Subgroup (DihedralGroup 6) where
  carrier := {r 0}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : bot = ⊥ := by ext x; rfl

-- Subgroups isomorphic to D3

--
def d3_1 : Subgroup (DihedralGroup 6) where
  carrier := {r 0, r 2, r 4, sr 0, sr 2, sr 4}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

theorem mem_d31_iff : g ∈ d3_1 ↔ g = r 0 ∨ g = r 2 ∨ g = r 4 ∨ g = sr 0 ∨ g = sr 2 ∨ g = sr 4 := by rfl

def d3_2 : Subgroup (DihedralGroup 6) where
  carrier := {r 0, r 2, r 4, sr 1, sr 3, sr 5}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : d3_1 ≃* DihedralGroup 3 where
  toFun := by
    intro x
    cases' x with g hg
    rw [mem_d31_iff] at hg
    sorry

  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

instance : MulAction (DihedralGroup 6) (ZMod 2) where
  smul := by
    intro g p
    cases' g with i j
    exact p
    exact -p
  one_smul := by decide
  mul_smul := by decide


instance : MulAction (DihedralGroup 6) (ZMod 6) where
  smul := by
    intro g p
    cases' g with i j

    -- ri ⬝ p
    exact i + p

    -- sr j ⬝ p
    exact - j - p
  one_smul := by decide
  mul_smul := by decide

open Polynomial Real Complex

instance : MulAction (DihedralGroup 6) ℂ where
  smul := by
    intro g z
    cases' g with i j

    -- ri ⬝ p
    exact z

    -- sr j ⬝ p
    exact -z
  one_smul := by
    intro b
    rfl
  mul_smul := by
    intro g1 g2 z
    cases' g1 with i j
    cases' g2 with i' j'
    rfl
    rfl
    cases' g2 with i' j'
    rfl
    simp
    sorry

instance : MulAction (DihedralGroup 6) ℂ where
  smul := by
    intro g p
    cases' g with i j

    -- ri ⬝ p
    exact (exp (2 * π * I * (i.val / 6)))

    -- sr j ⬝ p
    exact -(exp (2 * π * I * (j.val / 6)))
  one_smul := by sorry
  mul_smul := by sorry


-- https://kconrad.math.uconn.edu/blurbs/grouptheory/dihedral2.pdf
-- https://math.stackexchange.com/questions/1099579/why-are-automorphisms-of-d-2n-n-geq-5-odd-not-always-inner
