import Mathlib
import Canonical

example
  (X : Type)
  (IsLine : Finset X → Prop)
  (P Q : X)
  (l : Finset X)
  (hl : IsLine l)
  (hp : P ∈ l)
  (hq : Q ∈ l)
: IsLine l ∧ P ∈ l ∧ Q ∈ l := ⟨hl, hp, hq⟩
