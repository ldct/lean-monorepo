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

@[simp, norm_cast]
lemma BSubgroup.coe_mul {G} [Borcherds.Group G] (H : BSubgroup G) (a b : {x // x ∈ H.carrier}) :
    (↑(a * b) : G) = ↑a * ↑b := rfl

def ProductOfSubgroupsHom {G} [Borcherds.Group G] (H K : BSubgroup G) (h : HasCommutingSubgroups H K) :
(H × K) →* G where
  toFun := fun p => p.1 * p.2
  map_mul := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
    simp only [Prod.mk_mul_mk, BSubgroup.coe_mul]
    rw [Borcherds.Group.mul_assoc (p₁ : G) _ _, ← Borcherds.Group.mul_assoc (q₁ : G) _ _]
    have := h p₁ (by simp) p₂ (by simp)
    rw [h q₁ (by simp) p₂ (by simp)]
    simp [Borcherds.Group.mul_assoc]

def GroupHom.ker {G H} [Group G] [Group H] (φ : G →* H) : BSubgroup G where
  carrier := { x | φ.toFun x = 1 }
  one_mem := by
    simp only [Set.mem_setOf_eq]
    rw [φ.map_one]
  mul_mem := by
    intro x y hx hy
    simp_all [Set.mem_setOf_eq, φ.map_mul]
  inv_mem := by
    intro x hx
    simp_all only [Set.mem_setOf_eq]
    rw [φ.map_inv x, hx, Group.one_inv]

def Group.bot {G} [Group G] : BSubgroup G where
  carrier := {1}
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp

instance {G} [Group G] : Bot (BSubgroup G) where
  bot := Group.bot

lemma eq_bot_iff {G} [Group G] (H : BSubgroup G) : H = ⊥ ↔ H.carrier = {1} := by
  rw [show (⊥ : BSubgroup G) = Group.bot by rfl, Group.bot]
  constructor
  · intro h
    rw [h]
  · intro h
    ext g
    simp [h]

lemma GroupHom.injective_of_ker_trivial {G H} [Group G] [Group H] (φ : G →* H) (h : φ.ker = ⊥) : Function.Injective φ.toFun := by
  intro x₁ x₂ hx
  suffices h : x₁ * x₂⁻¹ = 1 by
    rw [show x₂ = 1 * x₂ by simp, ← h, Group.mul_assoc]
    simp
  have hx := congr($hx * (φ.toFun x₂)⁻¹)
  simp only [Group.mul_inv_cancel] at hx
  rw [← φ.map_inv, ← φ.map_mul] at hx
  have : (x₁ * x₂⁻¹) ∈ φ.ker.carrier := by
    simp [GroupHom.ker, hx]
  rw [show φ.ker.carrier = {1} by rw [(eq_bot_iff φ.ker).mp h]] at this
  simp_all

/-
The hard direction of the recognition theorem
-/
noncomputable def ProductOfSubgroups (G) [Borcherds.Group G] (J K : BSubgroup G)
    (h₁ : HasCommutingSubgroups J K) (h₂ : HasDecomposition J K) (h₃ : HasTrivialIntersection J K) :
  Borcherds.GroupIso (J × K) G := GroupHom.toGroupIso (ProductOfSubgroupsHom J K h₁) (by
    unfold Function.Bijective
    constructor
    · apply GroupHom.injective_of_ker_trivial
      rw [eq_bot_iff]
      simp only [GroupHom.ker, ProductOfSubgroupsHom]
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      unfold HasTrivialIntersection at h₃
      obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := g
      simp only [Prod.mk_eq_one]
      constructor
      · intro h
        have h := congr($h * (k)⁻¹)
        have h : j = k⁻¹ := by
          simp [Group.mul_assoc] at h
          exact h
        constructor
        · ext
          dsimp
          have : j ∈ J.carrier ∩ K.carrier := by
            simp only [Set.mem_inter_iff, hj, true_and]
            rw [h]
            simp [K.inv_mem _ hk]
          simp only [h₃, Set.mem_singleton_iff] at this
          rw [this]
          norm_cast
        · ext
          dsimp
          -- have h := congr((j)⁻¹ * $h)
          -- simp [← Group.mul_assoc] at h
          have : k ∈ J.carrier := by
            have h := congr($h⁻¹)
            simp [Group.inv_inv] at h
            rw [← h]
            have := J.inv_mem _ hj
            exact this
          have : k ∈ J.carrier ∩ K.carrier := by
            grind
          simp [h₃] at this
          rw [this]
          norm_cast
      · rintro ⟨ ⟨j, hj⟩, ⟨k, hk⟩⟩
        simp
    · intro g
      obtain ⟨j, hj, k, hk, rfl⟩ := h₂ g
      use ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
      simp [ProductOfSubgroupsHom]
  )

/-
1.3 - Quotient Groups
-/
