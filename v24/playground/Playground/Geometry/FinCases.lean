import Mathlib

/-
Tests of the `fin_cases` tactic.
-/

#check Fin.fintype
#eval List.finRange 3

instance (n : ℕ) : Fintype (Fin n) := {
  elems := ⟨List.finRange n, List.nodup_finRange n⟩
  complete := List.mem_finRange
}


example (g : ZMod 5) : (g*5 = 0) := by
  fin_cases g
  -- it's unfortunate that these have unapplied functions... but a dsimp gets rid of them
  <;> dsimp
  <;> decide

example (g : DihedralGroup 3) : (g^6 = 1) := by
  fin_cases g <;> simp
  -- yuck, fintypeHelper is exposed
  all_goals decide

namespace DihedralGroup

/-
One way to fix this is to define the Fintype instance without fintypeHelper
-/
instance : Fintype (DihedralGroup 3) := {
  elems := ⟨ Multiset.ofList [r 0, r 1, r 2, sr 0, sr 1, sr 2], sorry ⟩
  complete := sorry
}

example (g : DihedralGroup 3) : (g^6 = 1) := by
  fin_cases g
  all_goals decide

example (g : QuaternionGroup 2) : (g^9 = g) := by
  fin_cases g <;> simp
  all_goals decide
