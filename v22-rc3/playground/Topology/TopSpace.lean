import Mathlib

/-- A topology on `X`. -/
class TopSpace (X : Type) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen (⊤ : Set X)
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s : Set (Set X), (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

theorem TopSpace.isOpen_empty (X : Type) [T : TopSpace X] : TopSpace.IsOpen (∅ : Set X) := by
  let ι : Set (Set X) := ∅

  have := T.isOpen_sUnion ∅ (by
    intro t ht
    exfalso
    exact ht
  )
  simp at this
  exact this

-- The indiscrete topology on a type `X` is the topology where the only open sets are the empty set and the whole space.
instance Indiscrete (X : Type) : TopSpace X where
  IsOpen s := s = ∅ ∨ s = Set.univ
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by grind
  isOpen_sUnion I h := by grind

example (X : Type): (Indiscrete X).IsOpen ∅ := TopSpace.isOpen_empty X

class MyFilter (X : Type*) where
  sets : Set (Set X)
  univ_is : Set.univ ∈ sets
  finiteInter : ∀ s t, s ∈ sets → t ∈ sets → (s ∩ t) ∈ sets
  inclusion : ∀ s t, s ∈ sets → s ⊆ t → t ∈ sets

-- Exercise: if the empty set is in the filter, then the filter is trivial
example (X : Type*) (f : MyFilter X) (h_empty : ∅ ∈ f.sets) :
  ∀ S, S ∈ f.sets := by
  intro S
  exact f.inclusion ∅ S (by simp [h_empty]) (by simp)

#check Set.Ioi 3

def atTopℕ : MyFilter ℕ where
  sets := { s | ∃ b, Set.Ici b ⊆ s }
  univ_is := by
    use 0
    simp [Set.Ici]
  finiteInter s t hs ht := by
    obtain ⟨ n, hn ⟩ := hs
    obtain ⟨ m, hm ⟩ := ht
    use max n m
    grind [Set.Ici_inter_Ici]
  inclusion s t hs hst := by
    obtain ⟨ n, hn ⟩ := hs
    use n
    grind

#check Filter
#check Filter.atTop

instance : Preorder Empty where
  le a b := False
  le_refl a:= by trivial
  le_trans a b c := by trivial
  lt_iff_le_not_ge a b := by trivial

def atTopFilter (X : Type) [Preorder X] : MyFilter X where
  sets := {(s : Set X) | ∃ b : X, Set.Ioi b ⊆ s}
  univ_is := by
    simp
    use I.default
    simp
  finiteInter s t hs ht := by
    obtain ⟨ n, hn ⟩ := hs
    obtain ⟨ m, hm ⟩ := ht
    use max n m
    grind [Set.Ioi_inter_Ioi]
  inclusion s t hs hst := by
    obtain ⟨ n, hn ⟩ := hs
    use n
    grind


def tendsto (X Y : Type) (f : X → Y) (Nhdx : MyFilter X) (Nhdy : MyFilter Y) :
    Prop := ∀ V ∈ Nhdy.sets, f ⁻¹' V ∈ Nhdx.sets

theorem test1 (X : Type) (S₁ S₂ S: Set X) (h1 : S₁ ⊆ S) :
    S₁ ∩ S₂ ⊆ S := by
  grind

theorem test2 (X : Type) (S₁ S₂ S: Set X) (h1 : S₂ ⊆ S) :
    S₁ ∩ S₂ ⊆ S := by
  grind

/-- The neighborhood filter at a point `x` in a topological space `X` is the filter of sets `S` which satisfy either of the following equivalent conditions:
1. `S` contains an open set containing `x`.
2. `x` is in the interior of `S`
-/
def nhdsFilter (X : Type) [T : TopSpace X] (x : X) : MyFilter X where
  sets := {(T : Set X) | ∃ (S : Set X),
    TopSpace.IsOpen S ∧ S ⊆ T ∧ x ∈ S}
  univ_is := by
    use Set.univ
    and_intros
    exact T.isOpen_univ
    rfl
    trivial
  finiteInter := by
    intro s t hs ht
    obtain ⟨ S₁, hS₁, S₁_in_s, x_in_S₁ ⟩ := hs
    obtain ⟨ S₂, hS₂, S₂_in_t, x_in_S₂ ⟩ := ht
    use S₁ ∩ S₂
    rw [Set.subset_inter_iff]
    and_intros
    exact TopSpace.isOpen_inter S₁ S₂ hS₁ hS₂
    · apply test1
      exact S₁_in_s
    · apply test2
      exact S₂_in_t
    exact x_in_S₁
    exact x_in_S₂
  inclusion := by
    intro s t hs hst
    obtain ⟨ S, hS, S_in_s, x_in_S ⟩ := hs
    use S
    and_intros
    exact hS
    exact fun _ a_1 ↦ hst (S_in_s a_1)
    exact x_in_S

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

-- The excluded point topology on a type `X` with a distinguished point `x` is the topology where every set excluding `x` is open.
instance ExcludedPoint (X : Type) (x : X) : TopSpace X where
  IsOpen s := s = Set.univ ∨ x ∉ s
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by grind
  isOpen_sUnion I h := by grind

instance S1 : TopSpace (Fin 2) where
  IsOpen s := true
  isOpen_univ := by grind
  isOpen_sUnion := by grind
  isOpen_inter := by grind

instance (X : Type) (x y z : X) : TopSpace X where
  IsOpen s := s = Set.univ ∨ (x ∉ s ∧ y ∉ s ∧ z ∉ s)
  isOpen_univ := by simp
  isOpen_inter u v hu hv := by grind
  isOpen_sUnion I h := by grind


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

instance sierpinsky_1 : TopSpace (Fin 2) where
  IsOpen s := s = ∅ ∨ s = Set.univ ∨ s = {0}
  isOpen_univ := by simp

  isOpen_inter u v hu hv := by
    obtain hu | hu | hu := hu <;> obtain hv | hv := hv <;> simp [hu, hv] <;> tauto

  isOpen_sUnion I h := by
    have := enumerate I
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := this
    <;> simp_all
    <;> { grind }

def TopSpace.IsCoarser {X : Type} (T₁ T₂: TopSpace X) : Prop := ∀ x, (T₁.IsOpen x → T₂.IsOpen x)

example : S4.IsCoarser S1 := by
  intro x hx
  unfold TopSpace.IsOpen at *
  unfold S1 S4 at *
  dsimp at *

#check TopologicalSpace.IsTopologicalBasis



#synth UniformSpace ℝ

#check UniformSpace
