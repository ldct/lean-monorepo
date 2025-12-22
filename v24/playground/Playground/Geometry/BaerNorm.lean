import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-
The norm of a group G is the intersection of all normalizers of subgroups of G.
-/
def baerNorm (G : Type*) [Group G] : Subgroup G := ⨅ (H : Subgroup G), H.normalizer

/-
For an abelian group, the norm is the whole group.
-/
theorem groupNorm_eq_top_of_abelian {G : Type*} [CommGroup G] : baerNorm G = ⊤ := by
  -- Since G is abelian, every subgroup H of G is normal. Therefore, the normalizer of every subgroup H is G.
  have h_norm : ∀ H : Subgroup G, H.normalizer = ⊤ := by
    intros H
    -- Since G is abelian, every element of G normalizes every subgroup. Therefore, the normalizer of H is the entire group.
    ext g
    simp [Subgroup.normalizer];
  unfold baerNorm; aesop;

/-
The center of a group is contained in its norm.
-/
theorem center_le_groupNorm {G : Type*} [Group G] : Subgroup.center G ≤ baerNorm G := by
  intro x hx
  simp [baerNorm];
  simp_all +decide [ Subgroup.mem_center_iff, Subgroup.mem_iInf, Subgroup.mem_normalizer_iff ];
  simp +decide [ ← hx, mul_assoc ]

/-
The norm of a group is a normal subgroup.
-/
theorem groupNorm_normal {G : Type*} [Group G] : (baerNorm G).Normal := by
  -- Let φ be an automorphism of G.
  let norm : Subgroup G := baerNorm G;
  -- We want to show that groupNorm G is characteristic.
  have h_char : ∀ (phi : G ≃* G), ∀ x ∈ norm, phi x ∈ norm := by
    intro phi x hx
    simp [norm] at hx ⊢;
    -- We know that φ(N_G(H)) = N_G(φ(H)).
    have h_norm_eq : ∀ H : Subgroup G, (Subgroup.normalizer (H.map phi.toMonoidHom)) = (Subgroup.map phi.toMonoidHom (Subgroup.normalizer H)) := by
      exact fun H ↦ Eq.symm (Subgroup.map_equiv_normalizer_eq H phi);
    simp_all +decide [ baerNorm, Subgroup.mem_iInf ];
    intro H; specialize hx ( H.comap phi.toMonoidHom ) ; simp_all +decide [ Subgroup.mem_normalizer_iff ] ;
    intro h; specialize hx ( phi.symm h ) ; aesop;
  refine' ⟨ fun g hg => _ ⟩;
  exact fun h => h_char ( MulAut.conj h ) g hg

/-
An element is in the norm if and only if it normalizes every subgroup.
-/
theorem mem_groupNorm_iff {G : Type*} [Group G] (x : G) : x ∈ baerNorm G ↔ ∀ H : Subgroup G, x ∈ H.normalizer := by
  simp +decide [ baerNorm, Subgroup.mem_iInf]

theorem q8_norm_ne_center : baerNorm (QuaternionGroup 2) ≠ Subgroup.center (QuaternionGroup 2) := by
  have h_conj : ∀ x : QuaternionGroup 2, ∀ h : QuaternionGroup 2, x * h * x⁻¹ = h ∨ x * h * x⁻¹ = h⁻¹ := by
      decide
  have h_normal : ∀ H : Subgroup (QuaternionGroup 2), H.Normal := by
    intro H
    constructor
    intro n hn g
    specialize h_conj g n
    cases h_conj with
    | inl h1 => grind
    | inr h2 =>
      rw [← inv_mem_iff] at hn
      grind
  -- Since every subgroup of $Q_8$ is normal, the norm of $Q_8$ is the entire group.
  have h_norm : baerNorm (QuaternionGroup 2) = ⊤ := by
    simp +decide [ baerNorm, Subgroup.normalizer_eq_top ];
  simp_all [ Subgroup.eq_top_iff' ]
  simp_all (config := { decide := Bool.true }) only [Subgroup.ext_iff, true_iff, not_false_eq_true]
