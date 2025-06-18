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

    fin_cases i

    simp [toFun]

    have : r 1 ∉ d3_1 := by decide
    exfalso
    exact this hg

    simp [toFun]

    have : r 3 ∉ d3_1 := by
      decide
    exfalso
    exact this hg

    simp [toFun]

    have : r 5 ∉ d3_1 := by decide
    exfalso
    exact this hg

    fin_cases j
    simp [toFun]
    simp [toFun] at hg

    have : sr 1 ∉ d3_1 := by decide
    exfalso
    exact this hg

    simp [toFun]
    simp [toFun] at hg

    have : sr 3 ∉ d3_1 := by decide
    exfalso
    exact this hg

    simp [toFun]
    simp [toFun] at hg

    have : sr 5 ∉ d3_1 := by decide
    exfalso
    exact this hg

  right_inv := by
    intro g
    fin_cases g
    repeat decide

  map_mul' := by
    rintro ⟨v, dv⟩  y

    simp [toFun]

    repeat sorry

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
