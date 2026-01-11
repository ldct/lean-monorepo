import Mathlib

/-
Enumerations of finite sets.

Let `T` be some finite type (e.g. `Fin 2`). If we can prove theorems of the form `∀ x : T, x = 0 ∨ x = 1` via the `decide` tactic, this means there is a decision procedure registered with the `Decidable` typeclass, which typically operates by enumerating all the elements of `T`. Thus, we can prove theorems of the form `∀ x : T, P x` as well, subject to certain restrictions on `P`.

This file explores which types `T` have this property.
-/

/- Fin 1-/
example (I : Finset (Fin 1)) : I = {} ∨ I = {0} := by
  decide +revert

example (I : Finset (Finset (Fin 1))) :
  I = {} ∨ I = {{}} ∨ I = {{0}} ∨ I = {{}, {0}} := by
  decide +revert

/-
### Fin 2
-/
example (I : Finset (Fin 2)) : I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  decide +revert

example (I : Finset (Finset (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
  decide +revert

/-
## Replace `Finset` with `Set`, outside in
-/

example (I : Set (Finset (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
  have := Fintype.finsetEquivSet.surjective I
  obtain ⟨I, rfl⟩ := Fintype.finsetEquivSet.surjective I
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simpa using by decide +revert

example (I : Set (Set (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
  obtain ⟨I, rfl⟩ := (Fintype.finsetEquivSet.trans (Equiv.Set.congr Fintype.finsetEquivSet)).surjective I
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simpa [Set.image_insert_eq] using by decide +revert


abbrev a : Set (Fin 2) := {0, 1}
abbrev b : Set (Fin 2) := {1, 0}

example : a = b := by
  grind
