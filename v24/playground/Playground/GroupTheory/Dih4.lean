import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- The 10 subgroups of Dih4 - https://people.maths.bris.ac.uk/~matyd/GroupNames/1/D4.html

-- ⊥

def bot_4 : Subgroup (DihedralGroup 4) where
  carrier := {r 0}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

example : bot_4 = ⊥ := by ext x; rfl

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

def v1_4 : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 0, sr 2 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

def v2_4 : Subgroup (DihedralGroup 4) where
  carrier := { r 0, r 2, sr 1, sr 3 }
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

open Pointwise

def g_4 : ConjAct (DihedralGroup 4) := r 1
#eval g_4 • (r (0 : ZMod 4))
#eval g_4 • (r (2 : ZMod 4))
#eval g_4 • (sr (1 : ZMod 4))
#eval g_4 • (sr (3 : ZMod 4))

#eval Set.toFinset {1, 2}

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
  | sr 0 => isFalse (by rw [rot]; simp; decide)
  | sr 1 => isFalse (by rw [rot]; simp; decide)
  | sr 2 => isFalse (by rw [rot]; simp; decide)
  | sr 3 => isFalse (by rw [rot]; simp; decide)

-- TODO: fix for v4.24 (DihedralGroup.r_injective removed)
example {n : ℕ} {i : ZMod n} (h : (r i) = 1) : i = 0 := by
  sorry

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

example : Subgroup.closure {r (1 : ZMod 4)} = rot := by
  -- current goal is `⊢ Subgroup.closure {r 1} = rot`
  apply Subgroup.closure_eq_of_le
  intro x hx
  simp at hx
  subst hx
  exact (by decide : r 1 ∈ rot)

  intro x hx
  rw [rot] at hx
  have r_1_in_closure := Subgroup.mem_closure_singleton_self (r (1: ZMod 4))
  rcases hx with (h0 | h1 | h2 | h3)
  -- r 0 case
  rw [h0]
  exact Subgroup.one_mem _
  rw [h1]

  have r_1_in_closure := Subgroup.mem_closure_singleton_self (r (1: ZMod 4))

  -- r 1 case
  exact r_1_in_closure

  -- r 2 case
  have r_1_sq : (r (1 : ZMod 4))^2 ∈ Subgroup.closure {r 1} := by
    exact
    Subgroup.pow_mem (Subgroup.closure {r 1}) r_1_in_closure 2
  simp at r_1_sq
  rw [h2]
  exact r_1_sq

  -- r 3 case
  have r_1_cube : (r (1 : ZMod 4))^3 ∈ Subgroup.closure {r 1} := by
    exact
    Subgroup.pow_mem (Subgroup.closure {r 1}) r_1_in_closure 3
  simp at r_1_cube
  rw [h3]
  exact r_1_cube

example : Subgroup.IsCommutative rot where
  is_comm := .mk fun a => fun b => by
    fin_cases a <;> fin_cases b <;> decide
