import Playground.Borcherds.Part2
namespace Borcherds

-- https://ak2316.user.srcf.net/files/handouts/direct-products/direct-product.pdf

/-
The embedding of H₁ in H₁ × H₂
-/
def leftCopy (H₁ H₂ : Type*) [Group H₁] [Group H₂] : BSubgroup (H₁ × H₂) where
  carrier := { p | p.2 = 1 }
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp

/-
The embedding of H₂ in H₁ × H₂
-/
def rightCopy (H₁ H₂ : Type*) [Group H₁] [Group H₂] : BSubgroup (H₁ × H₂) where
  carrier := { p | p.1 = 1 }
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp

def HasTrivialIntersection {G} [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  H₁.carrier ∩ H₂.carrier = {1}

/-
The left copy and the right copy intersect trivially
-/
example (H₁ H₂ : Type*) [Group H₁] [Group H₂] : HasTrivialIntersection (leftCopy H₁ H₂) (rightCopy H₁ H₂) := by
  simp only [HasTrivialIntersection, leftCopy, rightCopy]
  ext i
  suffices i.2 = 1 ∧ i.1 = 1 ↔ i = 1 by simpa
  constructor
  · rintro ⟨h₁, h₂⟩
    ext <;> simp_all
  · rintro rfl
    simp

def HasDecomposition {G} [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  ∀ g : G, ∃ h₁ ∈ H₁.carrier, ∃ h₂ ∈ H₂.carrier, g = h₁ * h₂

/-
The left and right copies generate the group
-/
example (H₁ H₂ : Type*) [Group H₁] [Group H₂] : HasDecomposition (leftCopy H₁ H₂) (rightCopy H₁ H₂) := by
  simp only [HasDecomposition, leftCopy, rightCopy]
  intro g
  use ⟨g.1, 1⟩
  simp
  grind

def HasCommutingSubgroups {G} [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  ∀ h₁ ∈ H₁.carrier, ∀ h₂ ∈ H₂.carrier, h₁ * h₂ = h₂ * h₁

/-
The left and right copies commute
-/
example (H₁ H₂ : Type*) [Group H₁] [Group H₂] : HasCommutingSubgroups (leftCopy H₁ H₂) (rightCopy H₁ H₂) := by
  simp only [HasCommutingSubgroups, leftCopy, rightCopy]
  rintro ⟨h11, h12⟩ hh₁ ⟨h21, h22⟩ hh₂
  obtain rfl : h12 = 1 := by simp_all
  obtain rfl : h21 = 1 := by simp_all
  simp

/-
Definition: a group is isomorphic to the product of two of its subgroups
-/
def IsIsomorphicToProductOfSubgroups (G) [Borcherds.Group G] (H₁ H₂ : BSubgroup G) : Prop :=
  Nonempty (Borcherds.GroupIso (H₁ × H₂) G)

/-
The recognition theorem (← direction only).
The forward direction fails for the weak definition IsIsomorphicToProductOfSubgroups:
  Counterexample: G = K4, H₁ = H₂ = {1, a}. Then H₁ × H₂ ≅ Z/2 × Z/2 ≅ K4 = G,
  but H₁ ∩ H₂ = {1, a} ≠ {1}.
See IsIsomorphicToProductOfSubgroups' below for the corrected biconditional.
-/

/-
1.3 - Quotient Groups
-/
