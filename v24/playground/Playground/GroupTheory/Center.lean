import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

import Playground.GroupTheory.CentralizerOfRotations

namespace DihedralGroup

def B : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

theorem mem_B_iff (g : DihedralGroup 4) : g ∈ B ↔ g = r 0 ∨ g = r 2 := by
  rfl

example (h : (1 = 0 ∨ 1 = 2)) : False := by
  have h' : ¬(1 = 0 ∨ 1 = 2) := by decide
  exact h' h

theorem target : B = Subgroup.center (DihedralGroup 4) := by
  ext a
  rw [←Subgroup.mem_carrier]
  cases' a with i i
  fin_cases i

  simp
  constructor
  rw [←Subgroup.mem_carrier]
  intro h
  decide
  intro h
  rw [mem_B_iff]
  simp

  simp
  constructor

  intro h
  rw [mem_B_iff] at h
  simp at h
  exfalso

  revert h


  decide


  have e : ¬((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2) := by decide
  apply e
  exact h

  repeat sorry
