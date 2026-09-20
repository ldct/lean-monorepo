import Playground.Artin.Chapter_2_4_exercises

namespace Artin

variable {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂]

-- Definition 2.5.1
structure Hom (G₁ : Type*) [Group G₁] (G₂ : Type*) [Group G₂] where
  toFun : G₁ → G₂
  map_mul' : ∀ x y : G₁, toFun (x * y) = toFun x * toFun y
notation G₁ " →* " G₂ => Hom G₁ G₂

/-- Proposition 2.5.3b
Group homomorphisms map the identity to the identity -/
@[simp] lemma Hom.map_one (φ : G₁ →* G₂) : φ.toFun 1 = 1 := by
  have : (1 : G₁) * 1 = 1 := by simp
  have := congr(φ.toFun $this)
  rw [φ.map_mul'] at this
  have := congr((φ.toFun 1)⁻¹ * $this)
  simp only [artinGroupCancel, Group.inv_mul_cancel] at this
  exact this

/-- Proposition 2.5.3c
Group homomorphisms map inverses to inverses -/
lemma Hom.map_inv (φ : G₁ →* G₂) (x : G₁) : (φ.toFun x)⁻¹ = φ.toFun x⁻¹ := by
  rw [inv_eq_iff, ← φ.map_mul', Group.mul_inv_cancel, Hom.map_one]

def image (φ : G₁ →* G₂) : Subgroup G₂ where
  carrier := { y : G₂ | ∃ x : G₁, φ.toFun x = y }
  one_mem := by
    use 1
    simp
  mul_mem := by
    rintro y z ⟨x, hx⟩ ⟨z, hz⟩
    use x * z
    simp [← hx, ← hz, φ.map_mul']
  inv_mem := by
    rintro y ⟨x, hx⟩
    use x⁻¹
    simp [← hx, φ.map_inv]

def ker (φ : G₁ →* G₂) : Subgroup G₁ where
  carrier := { x : G₁ | φ.toFun x = 1 }
  one_mem := by
    simp
  mul_mem := by
    rintro x y hx hy
    simp at *
    simp_all [φ.map_mul']
  inv_mem := by
    rintro x hx
    simp_all [Set.mem_setOf_eq, ← φ.map_inv]
lemma mem_ker_iff (x : G₁) (φ : G₁ →* G₂) : x ∈ (ker φ).carrier ↔ φ.toFun x = 1 := by rfl

-- The left coset gH := { gh | h ∈ H }
def lcoset (g : G) (H : Subgroup G) : Set G :=
  H.carrier.image (fun h => g * h)
notation g " ⨀ " H => lcoset g H

lemma mem_lcoset {g x : G} {H : Subgroup G} :
    (x ∈ g ⨀ H) ↔ ∃ h ∈ H.carrier, g * h = x := by
  simp only [lcoset, Set.mem_image]

lemma mem_lcoset_self (g : G) (H : Subgroup G) : g ∈ (g ⨀ H) :=
  mem_lcoset.mpr ⟨1, H.one_mem, Group.mul_one g⟩

/- The type of left cosets of H in G -/
structure LeftCoset (H : Subgroup G) where
  carrier : Finset G
  is_coset : ∃ g, carrier = lcoset g H

-- Proposition 2.5.8, part 1 ↔ part 2
theorem im_eq_iff_mem_ker (a b : G₁) (φ : G₁ →* G₂) : φ.toFun a = φ.toFun b ↔ (a⁻¹ * b) ∈ (ker φ).carrier := by
  constructor
  · intro h
    have := congr((φ.toFun a)⁻¹ * $h)
    grind [Group.inv_mul_cancel, φ.map_inv, φ.map_mul', mem_ker_iff]
  · intro h
    rw [mem_ker_iff] at h
    have h := congr((φ.toFun a) * $h)
    rw [φ.map_mul', ← φ.map_inv] at h
    simp [artinGroupCancel] at h
    grind

-- Proposition 2.5.8, part 2 ↔ part 3
theorem mem_ker_iff_mem_coset (a b : G₁) (φ : G₁ →* G₂) : (a⁻¹ * b) ∈ (ker φ).carrier ↔ b ∈ a ⨀ (ker φ) := by
  constructor
  · intro h
    use a⁻¹ * b
    simp [h, artinGroupCancel]
  · intro h
    obtain ⟨g, ⟨h1, h2⟩ ⟩ := h
    dsimp at h2
    obtain rfl := h2
    simp_all [artinGroupCancel]

theorem part_4 (a b : G₁) (φ : G₁ →* G₂) : (b ∈ a ⨀ (ker φ)) ↔ (b ⨀ (ker φ)) ⊆ a ⨀ (ker φ) := by
  constructor
  · intro h g hg
    rw [mem_lcoset] at *
    obtain ⟨ k₁, hk₁, hk₂ ⟩ := h
    obtain ⟨ k₂, hk₃, hk₄ ⟩ := hg
    use a⁻¹ * g
    obtain rfl := hk₄
    obtain rfl := hk₂
    simp [artinGroupCancel]
    grind [Subgroup.mul_mem]
  · intro h
    have : b ∈ (b ⨀ (ker φ)) := by
      rw [mem_lcoset]
      use 1
      simp [Subgroup.one_mem]
    specialize h this
    exact h


def Subgroup.bot {G : Type*} [Group G] : Subgroup G where
  carrier := {1}
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp
lemma Subgroup.mem_bot_iff {G : Type*} [Group G] (i : G) : i ∈ Subgroup.bot.carrier ↔ i = 1 := by rfl


-- Corollary 2.5.9
example (φ : G₁ →* G₂) : Function.Injective φ.toFun ↔ ker φ = Subgroup.bot := by
  constructor
  · rintro h
    have : φ.toFun 1 = 1 := by simp
    ext g
    simp [Subgroup.mem_bot_iff]
    grind [Subgroup, mem_ker_iff]
  · intro h1 a b h2
    have h2 := congr((φ.toFun a)⁻¹ * $h2)
    simp at h2
    rw [φ.map_inv, ← φ.map_mul'] at h2
    symm at h2
    rw [← mem_ker_iff, h1, Subgroup.mem_bot_iff] at h2
    have h2 := congr(a * $h2)
    simp [artinGroupCancel] at h2
    grind

-- Definition 2.5.10
def Subgroup.IsNormal (N : Subgroup G) : Prop :=
  ∀ a ∈ N.carrier, ∀ g : G, g * a * g⁻¹ ∈ N.carrier

lemma Subgroup.isNormal_iff_mem_ker (N : Subgroup G) :



end Artin
