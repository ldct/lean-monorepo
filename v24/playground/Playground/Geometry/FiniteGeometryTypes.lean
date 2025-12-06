import Mathlib

namespace TypesFG


class IncidenceGeometry where
  Point : Type
  Line : Type
  IsOnLine : Point → Line → Prop

  -- For each two distinct points, there is a unique line containing both of them
  a1 : ∀ P Q, P ≠ Q → (∃! l, IsOnLine P l ∧ IsOnLine Q l)

  -- For every line there exists at least two distinct points on it
  a2 : ∀ l, ∃ P Q, P ≠ Q ∧ IsOnLine P l ∧ IsOnLine Q l

  -- There exists at least three distinct points
  a3 : ∃ P Q R : Point, P ≠ Q ∧ Q ≠ R ∧ P ≠ R

  -- Not all points lie on the same line
  a4 : ¬∃ l, ∀ P, IsOnLine P l

structure FSIG (X : Type) where
  IsLine : Finset X → Prop

  -- For each two distinct points, there is a unique line containing both of them
  a1 : ∀ P Q, P ≠ Q → (∃! l, IsLine l ∧ P ∈ l ∧ Q ∈ l)

  -- For every line there exists at least two distinct points on it
  a2 : ∀ l, IsLine l → ∃ P Q, P ≠ Q ∧ P ∈ l ∧ Q ∈ l

  -- There exists at least three distinct points
  a3 : ∃ P Q R : X, P ≠ Q ∧ Q ≠ R ∧ P ≠ R

  -- Not all points lie on the same line
  a4 : ¬∃ l, IsLine l ∧ ∀ P, P ∈ l

instance (X : Type) (fsig : FSIG X) : IncidenceGeometry where
  Point := X
  Line := { l : Finset X // fsig.IsLine l }
  IsOnLine P l := P ∈ l.val
  a1 P Q h := by
    have := fsig.a1 P Q h
    obtain ⟨ l, ⟨ ⟨ h1, h2, h3 ⟩, h4 ⟩ ⟩ := this
    dsimp at h
    use ⟨ l, h1 ⟩
    constructor
    exact ⟨ h2, h3 ⟩
    intro l' ⟨ h5, h6 ⟩
    rw [Subtype.ext_val_iff]
    specialize h4 l'
    apply h4
    and_intros
    exact l'.property
    exact h5
    exact h6
  a2 l := by sorry
  a3 := by sorry
  a4 := by sorry

-- 30k heartbeats
instance ThreePointGeometry : IncidenceGeometry where
  Point := Fin 3
  Line := {l : Finset (Fin 3) // l = {0, 1} ∨ l = {0, 2} ∨ l = {1, 2}}
  IsOnLine P l := P ∈ l.val
  a1 P Q h := by
    fin_cases P <;> fin_cases Q <;> dsimp at *
    all_goals try { exfalso; exact h rfl }
    · use ⟨ { 0, 1 }, by grind ⟩
      decide +revert
    · use ⟨ { 0, 2 }, by grind ⟩
      decide +revert
    · use ⟨ { 1, 0 }, by grind ⟩
      decide +revert
    · use ⟨ { 1, 2 }, by grind ⟩
      decide +revert
    · use ⟨ { 2, 0 }, by grind ⟩
      decide +revert
    · use ⟨ { 2, 1 }, by grind ⟩
      decide +revert
  a2 l := by decide +revert
  a3 := by decide
  a4 := by decide
