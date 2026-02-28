import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Playground.Geometry.ZMul

open Subgroup

variable {G : Type*} [Group G]

-- closure of S is the intersection of all subgroups
#check Subgroup.closure

-- the next two are D&F 1 (page 65)
example [Group G] (H : Subgroup G) : H ≤ Subgroup.closure H.carrier := by
  intro h h_in_H
  rw [mem_closure]
  intro G H_lt_G
  exact H_lt_G h_in_H

example [Group G] (H : Subgroup G) : Subgroup.closure H.carrier ≤ H := by
  apply sInf_le -- since closure is defined as an intersection, it suffices to show that H is one of the intersecting sets
  simp
  rfl

-- D&F 2, Mathlib proof
example [Group G] (A B : Set G) (A_le_B : A ≤ B) : Subgroup.closure A ≤ Subgroup.closure B := by
  exact Subgroup.closure_mono A_le_B

-- D&F 2, Direct proof
example [Group G] (A B : Set G) (A_le_B : A ≤ B) : Subgroup.closure A ≤ Subgroup.closure B := by
  intro g g_in_close_A
  rw [mem_closure]
  intro K
  rw [mem_closure] at g_in_close_A
  specialize g_in_close_A K
  intro B_in_K
  apply g_in_close_A
  exact fun ⦃a⦄ a_1 ↦ B_in_K (A_le_B a_1)

-- D&F 3
example [Group G] (H : Subgroup G) (H_comm : IsMulCommutative H) : IsMulCommutative (Subgroup.closure (H.carrier ∪ ↑(Subgroup.center G))) where
  is_comm := ⟨fun a b => by
    sorry⟩
