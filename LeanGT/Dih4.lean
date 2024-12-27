import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- The 10 subgroups of Dih4 - https://people.maths.bris.ac.uk/~matyd/GroupNames/1/D4.html

-- ⊥

def bot : Subgroup (DihedralGroup 4) where
  carrier := {r 0}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : bot = ⊥ := by ext x; rfl

-- Subgroups isomorphic to C2

-- 4 flips

def f1 : Subgroup (DihedralGroup 4) where
  carrier := { r 0 , sr 0 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def f2 : Subgroup (DihedralGroup 4) where
  carrier := { r 0 , sr 1 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def f3 : Subgroup (DihedralGroup 4) where
  carrier := { r 0 , sr 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def f4 : Subgroup (DihedralGroup 4) where
  carrier := { r 0 , sr 4 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

-- half-rotations, center

def c : Subgroup (DihedralGroup 4) where
  carrier := { r 0 , r 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

-- V4

def v1 : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 0, sr 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def v2 : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 1, sr 3 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

-- The subgroup of rotations

def rot : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 1, r 2, r 3 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

instance (g : DihedralGroup 4) : Decidable (g ∈ rot) :=
  match g with
  | r 0 => isTrue (by rw [rot]; simp)
  | r 1 => isTrue (by rw [rot]; simp)
  | r 2 => isTrue (by rw [rot]; simp)
  | r 3 => isTrue (by rw [rot]; simp)
  | sr 0 => isFalse (by rw [rot]; simp)
  | sr 1 => isFalse (by rw [rot]; simp)
  | sr 2 => isFalse (by rw [rot]; simp)
  | sr 3 => isFalse (by rw [rot]; simp)

example : IsCyclic (rot) := ⟨ ⟨r 1, by decide⟩, by
  intro x
  fin_cases x
  use 0
  rfl
  use 1
  rfl
  use 2
  rfl
  use 3
  rfl
⟩


example : c ≤ rot := by
  intro x hx
  have mem_c_iff : x ∈ c ↔ x = r 0 ∨ x = r 2 := by rfl
  have mem_rot_iff : x ∈ rot ↔ x = r 0 ∨ x = r 1 ∨ x = r 2 ∨ x = r 3 := by rfl
  rw [mem_c_iff] at hx
  rw [mem_rot_iff]
  tauto
