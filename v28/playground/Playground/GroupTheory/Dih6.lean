import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

def v1_6 : Subgroup (DihedralGroup 6) where
  carrier := { r 0, r 3, sr 0, sr 3 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def f : (DihedralGroup 6) →* (DihedralGroup 6) where
  toFun := fun x => x
  map_one' := by rfl
  map_mul' := by simp

#check f.ker

def v2_6 : Subgroup (DihedralGroup 6) where
  carrier := { r 0, r 3, sr 1, sr 4 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def g_6 : ConjAct (DihedralGroup 6) := r 1
#eval g_6 • (r (0 : ZMod 6))
#eval g_6 • (r (3 : ZMod 6))
#eval g_6 • (sr (0 : ZMod 6))
#eval g_6 • (sr (3 : ZMod 6))

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

-- the action where rotation does nothing
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

noncomputable instance : MulAction (DihedralGroup 6) ℂ where
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
