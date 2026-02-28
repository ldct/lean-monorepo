import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Playground.GroupTheory.Dih6

namespace DihedralGroup

-- The subgroups of Dih6 - https://people.maths.bris.ac.uk/~matyd/GroupNames/1/D6.html

-- ⊥

def bot_6 : Subgroup (DihedralGroup 6) where
  carrier := {r 0}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : bot_6 = ⊥ := by ext x; rfl

-- Subgroups isomorphic to D3

--
def d3_1 : Subgroup (DihedralGroup 6) where
  carrier := {r 0, r 2, r 4, sr 0, sr 2, sr 4}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

theorem mem_d31_iff (g : DihedralGroup 6) : g ∈ d3_1 ↔ g = r 0 ∨ g = r 2 ∨ g = r 4 ∨ g = sr 0 ∨ g = sr 2 ∨ g = sr 4 := by rfl

def e : DihedralGroup 6 := r 0

instance (g : DihedralGroup 6) : Decidable (g ∈ d3_1) :=
  match g with
  | r 0 => isTrue (by rw [mem_d31_iff]; decide)
  | r 2 => isTrue (by rw [mem_d31_iff]; decide)
  | r 4 => isTrue (by rw [mem_d31_iff]; decide)
  | sr 0 => isTrue (by rw [mem_d31_iff]; decide)
  | sr 2 => isTrue (by rw [mem_d31_iff]; decide)
  | sr 4 => isTrue (by rw [mem_d31_iff]; decide)
  | r 1 => isFalse (by rw [mem_d31_iff]; decide)
  | r 3 => isFalse (by rw [mem_d31_iff]; decide)
  | r 5 => isFalse (by rw [mem_d31_iff]; decide)
  | sr 1 => isFalse (by rw [mem_d31_iff]; decide)
  | sr 3 => isFalse (by rw [mem_d31_iff]; decide)
  | sr 5 => isFalse (by rw [mem_d31_iff]; decide)

def e' : d3_1 := ⟨ r 0, by decide ⟩

#eval e ∈ d3_1
#eval e' = e -- implicit coercion

def d3_2 : Subgroup (DihedralGroup 6) where
  carrier := {r 0, r 2, r 4, sr 1, sr 3, sr 5}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def toFun (g : d3_1) : DihedralGroup 3 := match g.val with
  | r 0 => r 0
  | r 2 => r 1
  | r 4 => r 2
  | sr 0 => sr 0
  | sr 2 => sr 1
  | sr 4 => sr 2
  | _ => r 0 -- junk

example : d3_1 ≃* DihedralGroup 3 where
  toFun := toFun
  invFun g := match g with
  | r 0 => ⟨r 0, by decide⟩
  | r 1 => ⟨r 2, by decide⟩
  | r 2 => ⟨r 4, by decide⟩
  | sr 0 => ⟨sr 0, by decide⟩
  | sr 1 => ⟨sr 2, by decide⟩
  | sr 2 => ⟨sr 4, by decide⟩

  left_inv := by
    rintro ⟨g, hg⟩
    cases' g with i j
    all_goals sorry

  right_inv := by
    intro g
    fin_cases g
    repeat decide

  map_mul' := by
    rintro ⟨v, dv⟩  y

    simp [toFun]

    repeat sorry

open Polynomial Real Complex

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
