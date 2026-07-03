import Mathlib
open Equiv Equiv.Perm
example {n:ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n) : σ⁻¹ (σ x) = x := by
  exact?
