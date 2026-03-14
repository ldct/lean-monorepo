import Mathlib
import Mathlib.Tactic.TFAE
import Playground.Geometry.Chapter_7_1

/-
Through this section R is a ring with identity 1 ≠ 0.
-/

/-
# Proposition 9 (part 1)

Let I be an ideal of R. I = R ↔ I contains a unit
-/

lemma ideal_is_top_iff_exists_mem_unit {R} [Ring R] (I : Ideal R)
: I = ⊤ ↔ (∃ u, IsUnit u ∧ u ∈ I) := by
  constructor
  · intro rfl
    use 1
    simp
  rintro ⟨ u, hu1, hu2 ⟩
  ext r
  simp only [Submodule.mem_top, iff_true]
  rw [isUnit_iff_exists] at hu1
  obtain ⟨ v, h1, h2 ⟩ := hu1
  rw [show r = r * (v * u) by simp [h2]]
  rw [show r * (v * u) = r * v * u by group]
  rw [show r * v * u = (r * v) • u by simp]
  apply Ideal.mul_mem_left
  exact hu2

#check Field

example {R} [CommSemiring R] [Nontrivial R] (hf : ¬IsField R) :
∃ (x : R) (_ : x ≠ 0), ¬IsUnit x := by exact Ring.exists_not_isUnit_of_not_isField hf

theorem isField_iff_forall_ne_zero_isUnit {R} [CommRing R] [Nontrivial R] :
    IsField R ↔ ∀ a : R, a ≠ 0 → IsUnit a := by
  constructor
  · intro hF a ha
    have ⟨b, hb⟩ := hF.mul_inv_cancel ha
    exact IsUnit.of_mul_eq_one _ hb
  · intro h
    exact {
      exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := mul_comm
      mul_inv_cancel := fun {a} ha => by
        obtain ⟨u, hu⟩ := h a ha
        exact ⟨↑(u⁻¹), by rw [← hu]; simp [Units.mul_inv]⟩
    }

lemma exists_nz_of_nz_ideal {R} [Ring R] (I : Ideal R) (h : ⊥ < I) : ∃ u, u ∈ I ∧ u ≠ 0 := by
  by_contra h2
  have h2 : ∀ x ∈ I, x = 0 := by simp_all
  have : I = ⊥ := by
    ext r
    grind [zero_mem, Submodule.mem_bot]
  order

/-
# Proposition 9 (part 2)

Assume R is commutative. Then R is a field ↔ its only ideals are 0 and R.
-/
example {R} [CommRing R] [Nontrivial R] : IsField R ↔ (∀ I : Ideal R, I = ⊤ ∨ I = ⊥) := by
  constructor
  -- in this branch: assume R is a field.
  -- then, every nonzero ideal contains a unit,
  · intro h I
    by_cases hI : I = ⊥
    · grind
    left
    have h' := h
    rw [isField_iff_forall_ne_zero_isUnit] at h
    have hI : ⊥ < I := by order
    obtain ⟨ u, hu1, hu2 ⟩ := exists_nz_of_nz_ideal I hI
    rw [ideal_is_top_iff_exists_mem_unit]
    use u
    grind

  -- in this branch: conversely, if 0 and R are the only ideals...
  intro h
  rw [isField_iff_forall_ne_zero_isUnit]
  intro u hu
  -- let u be any nonzero element of R
  have : Ideal.span {u} = ⊤ := by
    by_contra h2
    specialize h (Ideal.span {u})
    simp [h2] at h
    grind
  have : 1 ∈ Ideal.span {u} := by
    grind [Submodule.mem_top]
  rw [Ideal.mem_span_singleton] at this
  exact isUnit_of_dvd_one this

/-
# Equivalent ways to state that a subgroup is nontrivial
-/

example {G} [Group G] (S : Subgroup G)
: (⊥ < S ↔ ⊥ ≠ S) := by grind [Ne.bot_lt']

example {G} [Group G] (S : Subgroup G)
: (⊥ < S → Nontrivial S) := by
  grind [Subgroup.bot_or_nontrivial S]

example {G} [Group G] (S : Subgroup G)
: (Nontrivial S → ∃ u, u ∈ S ∧ u ≠ 1) := by
  intro h
  apply Subgroup.exists_ne_one_of_nontrivial

example {G} [Group G] (S : Subgroup G)
  (h : ⊥ < S)
: ∃ u, u ∈ S ∧ u ≠ 1 := by
  have : Nontrivial S := by
    grind [Subgroup.bot_or_nontrivial S]
  apply Subgroup.exists_ne_one_of_nontrivial

lemma subgroup_bot_tfae {G} [Group G] (S : Subgroup G)
: List.TFAE [
  ⊥ < S,
  ⊥ ≠ S,
  Nontrivial S,
  ∃ u, u ∈ S ∧ u ≠ 1
] := by
  tfae_have 1 → 2 := by order
  tfae_have 2 → 3 := by grind [Subgroup.bot_or_nontrivial S]
  tfae_have 3 → 4 := by intro h; apply Subgroup.exists_ne_one_of_nontrivial
  tfae_have 4 → 1 := by
    grind [bot_lt_iff_ne_bot, Subgroup.mem_bot]
  tfae_finish

variable {G} [Group G] (S : Subgroup G) in
#check List.TFAE.out (subgroup_bot_tfae S) 0 2

/-
# Equivalent ways to state that an ideal is nontrivial
-/

lemma ideal_bot_tfae {R} [Ring R] (I : Ideal R)
: List.TFAE [
  ⊥ < I,
  ⊥ ≠ I,
  Nontrivial I,
  ∃ u, u ∈ I ∧ u ≠ 0
] := by
  tfae_have 1 → 2 := by order
  tfae_have 2 → 3 := by rw [Submodule.nontrivial_iff_ne_bot]; exact Ne.symm
  tfae_have 3 → 4 := by
    intro h
    rw [Submodule.nontrivial_iff_ne_bot] at h
    exact (Submodule.ne_bot_iff I).mp h
  tfae_have 4 → 1 := by
    grind [bot_lt_iff_ne_bot, Submodule.mem_bot]
  tfae_finish

/-
# Kernel of a ring homomorphism that does not preserve the multiplicative identity
-/
def nonunital_kernel {R S} [Ring R] [Ring S] (φ : R →ₙ+* S)
: Ideal R where
  carrier := { r | φ r = 0 }
  add_mem' := by
    intro a b ha hb
    simp_all only [Set.mem_setOf_eq]
    rw [map_add φ a b,ha, hb, add_zero]
  zero_mem' := by
    simp [map_zero φ]
  smul_mem' c x hx := by
    simp_all only [Set.mem_setOf_eq]
    simp [hx, mul_zero]

#check RingHom.ker

/-
# Corollary 10. If R is a field then any nonzero ring homomorphism from R into another ring is an injection.

Proof does not reflect D&F proof
-/

#check RingHomClass

#check RingHom.ker
#check TwoSidedIdeal.ker

def ker' {R S} [CommRing R] [Ring S] (φ : R →ₙ+* S) := (TwoSidedIdeal.ker φ).asIdeal


lemma cor_10 {F R} [Field F] [Ring R] (φ : F →ₙ+* R) (h : φ ≠ 0) : Function.Injective φ := by
  intro a b hab
  -- suffices: if φ x = 0 then x = 0
  suffices hinj : ∀ x, φ x = 0 → x = 0 by
    have : φ (a - b) = 0 := by simp [map_sub, hab]
    exact sub_eq_zero.mp (hinj _ this)
  -- The kernel of φ is an ideal of F
  intro x hx
  set K := nonunital_kernel φ with hK_def
  -- Since F is a field, K = ⊥ or K = ⊤
  have mem_K : ∀ y, y ∈ K ↔ φ y = 0 := by
    intro y; exact Iff.rfl
  rcases Ideal.eq_bot_or_top K with hbot | htop
  · -- K = ⊥, so x ∈ K means x = 0
    have : x ∈ K := (mem_K x).mpr hx
    rw [hbot] at this
    simpa using this
  · -- K = ⊤ means φ maps everything to 0, so φ = 0, contradiction
    exfalso
    apply h
    ext y
    have : y ∈ K := by rw [htop]; trivial
    simp [NonUnitalRingHom.zero_apply, (mem_K y).mp this]

lemma cor_10' {F R} [Field F] [NonUnitalRing R] (φ : F →ₙ+* R) (h : φ ≠ 0) : Function.Injective φ := by
  sorry

#check Ideal.IsMaximal

/-
# Remark - a NonUnitalRing need not have maximal ideals, but a unital ring always has maximal ideals
-/
