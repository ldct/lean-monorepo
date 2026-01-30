import Mathlib

/-
IsDedekindFiniteMonoid exists in recent Mathlib, but not v24
-/

def IsDedekindFinite (R) [Ring R] : Prop :=
  ∀ a b : R, a * b = 1 → b * a = 1

example : IsDedekindFinite (Matrix (Fin 2) (Fin 2) ℤ) := by
  intro a b h
  exact Matrix.mul_eq_one_comm.mp h

example {R} [CommRing R] : IsDedekindFinite R := by
  intro a b h
  exact mul_comm a b ▸ h
