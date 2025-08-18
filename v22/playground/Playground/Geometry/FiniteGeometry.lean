import Mathlib
import Canonical

namespace FinsetFG

class IncidenceGeometry (X : Type) where
  IsLine : Finset X → Prop

  -- For each two distinct points, there is a unique line containing both of them
  a1 : ∀ P Q, P ≠ Q → (∃! l, IsLine l ∧ P ∈ l ∧ Q ∈ l)

  -- For every line there exists at least two distinct points on it
  a2 : ∀ l, IsLine l → ∃ P Q, P ≠ Q ∧ P ∈ l ∧ Q ∈ l

  -- There exists at least three distinct points
  a3 : ∃ P Q R : X, P ≠ Q ∧ Q ≠ R ∧ P ≠ R

  -- Not all points lie on the same line
  a4 : ¬∃ l, IsLine l ∧ ∀ P, P ∈ l

-- 4k heartbeats
instance ThreePointGeometry : IncidenceGeometry (Fin 3) where
  IsLine s := s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2}
  a1 P Q h := by
    fin_cases P <;> fin_cases Q <;> dsimp at *
    all_goals try { exfalso; exact h rfl }
    · use {0, 1}
      decide
    · use {0, 2}
      decide
    · use {0, 1}
      decide
    · use {1, 2}
      decide
    · use {0, 2}
      decide
    · use {1, 2}
      decide
  a2 l hl := by decide +revert
  a3 := by decide
  a4 := by decide

instance FourPointGeometry : IncidenceGeometry (Fin 4) where
  IsLine s := s = {0, 1} ∨ s = {0, 2} ∨ s = {0, 3} ∨ s = {1, 2} ∨ s = {1, 3} ∨ s = {2, 3}
  a1 P Q h := by
    fin_cases P <;> fin_cases Q <;> dsimp at *
    all_goals try { exfalso; exact h rfl }
    · use {0, 1}
      decide
    · use {0, 2}
      decide
    · use {0, 3}
      decide
    · use {1, 0}
      decide
    · use {1, 2}
      decide
    · use {1, 3}
      decide
    · use {2, 0}
      decide
    · use {2, 1}
      decide
    · use {2, 3}
      decide
    · use {3, 0}
      decide
    · use {3, 1}
      decide
    · use {3, 2}
      decide
  a2 l hl := by decide +revert
  a3 := by decide
  a4 := by decide

instance FourPointGeometry' : IncidenceGeometry (Fin 4) where
  IsLine s := s.card = 2
  a1 P Q h := by
    use {P, Q}
    and_intros
    · rw [Finset.card_eq_two]
      grind
    · grind
    · grind
    intro l ⟨ h1, h2, h3 ⟩
    rw [Finset.card_eq_two] at h1
    grind
  a2 l hl := by
    obtain ⟨ x, y, hxy, h ⟩ := Finset.card_eq_two.mp hl
    use x, y
    grind
  a3 := by
    use 0, 1, 2
    decide
  a4 := by
    by_contra!
    obtain ⟨ l, hl, h ⟩ := this
    let s : Finset (Fin 4) := {0, 1, 2, 3}
    have h1 : s ⊆ l := by grind
    have h2 : s.card = 4 := by decide
    have := Finset.card_le_card h1
    simp_all

instance FivePointGeometry : IncidenceGeometry (Fin 5) where
  IsLine s := s.card = 2
  a1 P Q h := by
    use {P, Q}
    and_intros
    · rw [Finset.card_eq_two]
      grind
    · grind
    · grind
    intro l ⟨ h1, h2, h3 ⟩
    rw [Finset.card_eq_two] at h1
    grind
  a2 l hl := by
    obtain ⟨ x, y, hxy, h ⟩ := Finset.card_eq_two.mp hl
    use x, y
    grind
  a3 := by
    use 0, 1, 2
    decide
  a4 := by
    by_contra!
    obtain ⟨ l, hl, h ⟩ := this
    let s : Finset (Fin 5) := {0, 1, 2}
    have h1 : s ⊆ l := by grind
    have h2 : s.card = 3 := by decide
    have := Finset.card_le_card h1
    simp_all

instance NearPencil4 : IncidenceGeometry (Fin 4) where
  IsLine s := s = {1, 2, 3} ∨ s = {0 , 1} ∨ s = {0, 2} ∨ s = {0, 3}
  a1 P Q h := by
    fin_cases P <;> fin_cases Q <;> dsimp at *
    all_goals try { exfalso; exact h rfl }
    all_goals try { use {1, 2, 3}; decide }
    · use {0, 1}
      decide
    · use {0, 2}
      decide
    · use {0, 3}
      decide
    · use {0, 1}
      decide
    · use {0, 2}
      decide
    · use {0, 3}
      decide
  a2 l hl := by decide +revert
  a3 := by decide
  a4 := by decide


instance DoubleNearPencil4 : IncidenceGeometry (Fin 5) where
  IsLine s := s = {2, 3, 4} ∨ s = {0, 2} ∨ s = {0, 3} ∨ s = {0, 4} ∨ s = {1, 2} ∨ s = {1, 3} ∨ s = {1, 4} ∨ s = {0, 1}
  a1 P Q h := by
    fin_cases P <;> fin_cases Q <;> dsimp at *
    all_goals try { exfalso; exact h rfl }
    all_goals try { use {2, 3, 4}; decide }
    all_goals try { use {0, 1}; decide }
    all_goals try { use {0, 2}; decide }
    all_goals try { use {0, 3}; decide }
    all_goals try { use {0, 4}; decide }
    all_goals try { use {1, 2}; decide }
    all_goals try { use {1, 3}; decide }
    all_goals try { use {1, 4}; decide }
  a2 l hl := by decide +revert
  a3 := by decide
  a4 := by decide



def IncidenceGeometry.Intersects {X : Type} [IncidenceGeometry X] (l₁ l₂ : Finset X) : Prop :=
  ∃ P, P ∈ l₁ ∧ P ∈ l₂

def IncidenceGeometry.Collinear {X : Type} [IncidenceGeometry X] (P Q R : X) : Prop :=
  ∃ l, IsLine l ∧ P ∈ l ∧ Q ∈ l ∧ R ∈ l

-- Incidence theorem 1  / Theorem 1.4.4 / Any two distinct lines intersect in exactly one point
lemma IncidenceGeometry.intersect_one_point (X : Type) [IncidenceGeometry X]
  (l₁ l₂ : Finset X)
  (h_ne : l₁ ≠ l₂)
  (h₁ : IsLine l₁) (h₂ : IsLine l₂)
  (h : Intersects l₁ l₂)
: ∃! P, P ∈ l₁ ∧ P ∈ l₂ := by
  obtain ⟨ P, h1, h2 ⟩ := h
  use P
  and_intros
  · exact h1
  · exact h2
  · intro Q hQ
    by_contra P_ne_Q
    obtain ⟨ l, h', h'' ⟩ :=  a1 P Q (by exact fun a ↦ P_ne_Q (Eq.symm a))
    have ha := h'' l₁ (by grind)
    have hb := h'' l₂ (by grind)
    exact h_ne (by simp only [ha, hb])

-- Theorem 1.4.5
lemma IncidenceGeometry.exists_point_not_on_line {X : Type} [IncidenceGeometry X]
  (l : Finset X)
  (h : IsLine l)
: ∃ P, P ∉ l := by
  by_contra! h
  apply @a4 X
  use l

lemma eq_of_exists_unique
  {X : Type}
  {P : X → Prop}
  (h1 : ∃! t, P t)
  (x y : X)
  (hx : P x)
  (hy : P y)
: x = y := by
  exact ExistsUnique.unique h1 hx hy


lemma test (α : Type) (p : α → Prop)
    (h : ∃! x, p x) (y₁ y₂ : α) (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ := by
  exact ExistsUnique.unique h py₁ py₂

example (α : Type) (p : α → Prop)
    (h : ∃! x, p x) (y₁ y₂ : α) (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ := by
  exact test α p h y₁ y₂ py₁ py₂

example (α : Type) (p : α → Prop)
    (h : ∃! x, p x) (y₁ y₂ : α) (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ := by
  canonical [ExistsUnique.unique]




-- Given a line l and two points P and Q on l, if P, Q, R are collinear, then R is on l
lemma IncidenceGeometry.test1 {X : Type} [IncidenceGeometry X]
  {P Q R : X}
  (hc : Collinear P Q R)
  (h : P ≠ Q)
  {l : Finset X}
  (hl : IsLine l)
  (hp : P ∈ l)
  (hq : Q ∈ l)
: R ∈ l := by
  obtain ⟨ l', hl', hp', hq', hr' ⟩ := hc
  have := eq_of_exists_unique (a1 P Q h) l l' (by

    grind)
    (by grind)
  rw [this]
  exact hr'


-- Theorem 1.4.6
lemma IncidenceGeometry.test (X : Type) [IncidenceGeometry X]
  (P Q : X)
  (hne : P ≠ Q) :
∃ R, ¬ Collinear P Q R := by
  obtain ⟨ l, ⟨h1, h2, h3⟩, _ ⟩ := a1 P Q hne
  obtain ⟨ R, hR ⟩  := exists_point_not_on_line l h1
  use R
  by_contra h
  apply hR
  exact test1 h hne h1 h2 h3
