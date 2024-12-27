import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- actions of Dih6
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

-- show that D6 acts on a set of size 5 (e.g. ZMod 3 + ZMod 2)

-- https://kconrad.math.uconn.edu/blurbs/grouptheory/dihedral2.pdf
-- https://math.stackexchange.com/questions/1099579/why-are-automorphisms-of-d-2n-n-geq-5-odd-not-always-inner
