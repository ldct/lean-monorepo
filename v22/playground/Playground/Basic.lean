import Mathlib

example : (3/5 : ℚ).den = 5 := by norm_num




structure Dyadic where
  q : ℚ
  den_pow_2 : q.den.isPowerOfTwo

def d := Dyadic.mk (3/8) (by norm_num; use 3)

instance : Semigroup Dyadic where
  mul a b :=
    Dyadic.mk (a.q * b.q) (by
      sorry)
  mul_assoc := sorry

#check d

class IncidenceGeometry (X : Type) where
  IsLine : Set X → Prop
  -- For each two distinct points, there is a unique line containing both of them
  a1 : ∀ P Q, P ≠ Q → (∃! l, IsLine l ∧ P ∈ l ∧ Q ∈ l)

  -- For every line there exists at least two distinct points on it
  a2 : ∀ l, IsLine l → ∃ P Q, P ≠ Q ∧ P ∈ l ∧ Q ∈ l

  -- There exists at least three distinct points
  a3 : ∃ P Q R : X, P ≠ Q ∧ Q ≠ R ∧ P ≠ R

  -- Not all points lie on the same line
  a4 : ¬∃ l, IsLine l ∧ ∀ P, P ∈ l

lemma a1_aux (P Q : Fin 3) (h : P ≠ Q) :
 ∃! l : Set (Fin 3), (l = ({0, 1} : Set (Fin 3)) ∨ l = ({0, 2} : Set (Fin 3)) ∨ l = ({1, 2} : Set (Fin 3))) ∧ P ∈ l ∧ Q ∈ l := by
  fin_cases P <;> fin_cases Q <;> dsimp at *
  all_goals try { exfalso; exact h rfl }
  · use {0, 1}
    and_intros <;> grind
  · use {0, 2}
    and_intros <;> grind
  · use {0, 1}
    and_intros <;> grind
  · use {1, 2}
    and_intros <;> grind
  · use {0, 2}
    and_intros <;> grind
  · use {1, 2}
    and_intros <;> grind

instance ThreePointGeometry : IncidenceGeometry (Fin 3) where
  IsLine s := s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2}
  a1 P Q h := by
    apply a1_aux P Q h
  a2 l hl := by
    obtain h | h | h := hl
    · use 0, 1
      and_intros <;> grind
    · use 0, 2
      and_intros <;> grind
    · use 1, 2
      and_intros <;> grind
  a3 := by
    use 0, 1, 2
    simp
  a4 := by
    by_contra h
    obtain ⟨ l, h1, h2 ⟩ := h
    obtain h | h | h := h1
    · specialize h2 2
      rw [h] at h2
      simp at h2
    · specialize h2 1
      rw [h] at h2
      simp at h2
    · specialize h2 0
      rw [h] at h2
      simp at h2


class AffinePlane (X : Type) where
  IsLine : Set X → Prop
  a1 : ∀ P Q, P ≠ Q → (∃! l : Set X, IsLine l ∧ P ∈ l ∧ Q ∈ l)
  a2 : ∀ P l, IsLine l → P ∉ l → ∃! m, P ∈ m ∧ IsLine m ∧ (m = l ∨ (m ∩ l) = ∅)


/-- A topology on `X`. -/
class TopSpace (X : Type) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen (⊤ : Set X)
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s : Set (Set X), (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

-- class FinTopSpace (n : Nat) where
--   IsOpen : Finset (Fin n) → Prop
--   isOpen_univ : IsOpen (⊤ : Finset (Fin n))
--   isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
--   isOpen_sUnion : ∀ s : Finset (Finset (Fin n)), (∀ t ∈ s, IsOpen t) → IsOpen (⋃ s)

instance S1 : TopSpace (Fin 2) where
  IsOpen s := true
  isOpen_univ := by grind
  isOpen_sUnion := by grind
  isOpen_inter := by grind

example
  (I : Fin 2)
: I = 0 ∨ I = 1 := by
  grind

example
  (I : Finset (Fin 2))
: I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  decide +revert

example
  (X : Type)
  (I : Set (Set X))
  (h : ∀ t ∈ I, t = ⊥ ∨ t = ⊤)
: I = {} ∨ I = {⊤} ∨ I = {⊥} ∨ I = {⊥, ⊤} := by
  sorry

example
  (I : Set (Fin 2))
: I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  obtain ⟨I, rfl⟩ := Fintype.finsetEquivSet.surjective I
  simpa using by decide +revert

example
  (I : Set (Fin 2))
: I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  have := Fintype.finsetEquivSet.surjective I
  obtain ⟨I', h⟩ := this
  rw [← h]
  simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
  simp
  clear h I
  fin_cases I'
  <;> decide


theorem enumerate (I : Set (Set (Fin 2))) :
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

attribute [grind =] Set.inter_self

instance S4 : TopSpace (Fin 2) where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by grind
  isOpen_sUnion I h := by grind

-- The indiscrete topology on a type `X` is the topology where the only open sets are the empty set and the whole space.
instance Indiscrete (X : Type) : TopSpace X where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by grind
  isOpen_sUnion I h := by grind


-- The discrete topology on a type `X` is the topology where every subset is open.
instance Discrete (X : Type) : TopSpace X where
  IsOpen s := true
  isOpen_univ := by rfl
  isOpen_inter u v hu hv := by rfl
  isOpen_sUnion I h := by rfl

-- The included point topology on a type `X` with a distinguished point `x` is the topology where every set containing `x` is open.
instance IncludedPoint (X : Type) (x : X) : TopSpace X where
  IsOpen s := s = ∅ ∨ x ∈ s
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by grind
  isOpen_sUnion I h := by grind

-- The excluded point topology on a type `X` with a distinguished point `x` is the topology where every set containing `x` is open.
instance ExcludedPoint (X : Type) (x : X) : TopSpace X where
  IsOpen s := s = Set.univ ∨ x ∉ s
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by grind
  isOpen_sUnion I h := by grind


/-- A topology on `X`. -/
class TopSpace' (X : Type) where
  open_sets : Set (Set X)
  isOpen_univ : ⊤ ∈ open_sets
  isOpen_inter : ∀ s t, s ∈ open_sets → t ∈ open_sets → (s ∩ t) ∈ open_sets
  isOpen_sUnion : ∀ s : Set (Set X), (∀ t ∈ s, t ∈ open_sets) → (⋃₀ s) ∈ open_sets

instance S7 : TopSpace (Fin 3) where
  IsOpen s := s = ⊥ ∨ 0 ∈ s
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv]

  isOpen_sUnion I h := by
    simp [h]
    by_cases h' : ((∀ s ∈ I, s = ∅))
    . left
      exact h'
    simp at h'
    obtain ⟨ x, hx ⟩ := h'
    right
    use x
    constructor
    . exact hx.1
    specialize h x hx.1
    simp [hx] at h
    exact h


instance S7' : TopSpace' (Fin 3) where
  open_sets := { ⊥ } ∪ { s | 0 ∈ s }
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by
    obtain hu | hu := hu <;> obtain hv | hv := hv <;> simp_all
  isOpen_sUnion I h := by sorry



theorem set_univ : (Set.univ : Set (Fin 2)) = {1, 0} := by
  ext x
  simp
  fin_cases x <;> simp

instance sierpinsky_1 : TopSpace (Fin 2) where
  IsOpen s := s = ⊥ ∨ s = ⊤ ∨ s = {0}
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv] <;> tauto

  isOpen_sUnion I h := by
    have := enumerate I
    obtain hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI | hI := this
    <;> simp_all [h, hI]
    <;> { right; rw [set_univ] }

def TopSpace.IsCoarser {X : Type} (T₁ T₂: TopSpace X) : Prop := ∀ x, (T₁.IsOpen x → T₂.IsOpen x)

example : S4.IsCoarser S1 := by
  intro x hx
  unfold TopSpace.IsOpen at *
  unfold S1 S4 at *
  dsimp at *

#check TopologicalSpace.IsTopologicalBasis



#synth UniformSpace ℝ

#check UniformSpace


example (I : Finset (Fin 2)) : I = {} ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  decide +revert

example (I : Finset (Fin 1)) : I = {} ∨ I = {0} := by
  decide +revert

example (I : Finset (Finset (Fin 1))) :
  I = {} ∨ I = {{}} ∨ I = {{0}} ∨ I = {{}, {0}} := by
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

example (I : Set (Finset (Fin 2))) :
    I = {} ∨
    I = {{}} ∨ I = {{0}} ∨ I = {{1}} ∨ I = {{0, 1}} ∨
    I = {{}, {0}} ∨ I = {{}, {1}} ∨ I = {{}, {0, 1}} ∨
    I = {{0}, {1}} ∨ I = {{0}, {0, 1}} ∨ I = {{1}, {0, 1}} ∨
    I = {{}, {0}, {1}} ∨ I = {{}, {0}, {0, 1}} ∨ I = {{}, {1}, {0, 1}} ∨
    I = {{0}, {1}, {0, 1}} ∨
    I = {{}, {0}, {1}, {0, 1}} := by
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



structure Point where
  x : ℝ
  y : ℝ

instance Point.instSetoid : Setoid Point where
  r a b := a.x = b.x
  iseqv := {
    refl := by
      intro ⟨a, b⟩
      dsimp
    symm := by
      intro ⟨a, b⟩ ⟨c, d⟩ h
      linarith
    trans := by
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2
      simp at h1 h2 ⊢
      exact h1.trans h2
    }
