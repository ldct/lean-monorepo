import Mathlib

set_option maxRecDepth 512

open scoped Pointwise

-- #check EuclideanSpace

abbrev MAT3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev O3 := Matrix.orthogonalGroup (Fin 3) ℝ

example : Group O3 := by infer_instance

/-
This file formalizes the definitions and theorems from Norbert Peyerimhoﬀ
-/

/-
Definition 1.1 (page 2). A function f : ℝⁿ → ℝⁿ is called an isometry if f is surjective and it preserves distances.
-/
@[ext, grind ext]
structure RealIsometry (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  is_isometry : ∀ x y, ‖toFun x - toFun y‖ = ‖x - y‖
  surjective : Function.Surjective toFun

abbrev PlaneIsometry := RealIsometry 2
abbrev SpaceIsometry := RealIsometry 3

/-
Lemma 1.2. Every isometry is injective.
-/
@[grind .] theorem RealIsometry.injective {n : ℕ} (f : RealIsometry n) : Function.Injective f.toFun := by
  intro x y hxy
  have := calc
    0 = ‖f.toFun x - f.toFun y‖ := by grind [norm_eq_zero]
    _ = ‖x - y‖ := by rw [f.is_isometry]
  grind [norm_eq_zero]

/-
Prerequisite for lemma 1.3 If f is an isometry, then f⁻¹ exists.
-/
example {n : ℕ} (f : RealIsometry n) : Function.Bijective f.toFun := by grind [Function.Bijective]

noncomputable def RealIsometry.toEquiv {n : ℕ} (f : RealIsometry n) : Equiv.Perm (EuclideanSpace ℝ (Fin n)) where
  toFun := f.toFun
  invFun := f.toFun.invFun
  left_inv := by
    intro x
    have := Function.leftInverse_invFun f.injective
    simp_all [ Function.LeftInverse]
  right_inv := by
    intro x
    have := Function.rightInverse_invFun f.surjective
    simp_all [Function.RightInverse, Function.LeftInverse]

/-
Lemma 1.3 If f is an isometry, so is f⁻¹.
-/
noncomputable def RealIsometry.inverse {n : ℕ} (f : RealIsometry n) : RealIsometry n where
  toFun := f.toEquiv.symm
  is_isometry x y := calc
      ‖Function.invFun f.toFun x - Function.invFun f.toFun y‖ = ‖f.toFun (Function.invFun f.toFun x) - f.toFun (Function.invFun f.toFun y)‖ := by
        rw [← f.is_isometry]
      _ = ‖x - y‖ := by
        have : Function.RightInverse (Function.invFun f.toFun) f.toFun:= Function.rightInverse_invFun f.surjective
        simp_all [Function.RightInverse, Function.LeftInverse]
  surjective := by
    grind [Equiv.surjective]


def RealIsometry.identity {n : ℕ} : RealIsometry n where
  toFun := id
  is_isometry := by grind
  surjective := Function.surjective_id

example (v : R3) : ‖v‖^2 = v ⬝ᵥ v := by
  simp [EuclideanSpace.norm_sq_eq]
  simp [dotProduct]
  grind

theorem norm_orthogonal (n : ℕ)
  (A : Matrix.orthogonalGroup (Fin n) ℝ)
  (v : EuclideanSpace ℝ (Fin n))
: ‖A • v‖ = ‖v‖ := by
  have := A.2.2;
  rw [ EuclideanSpace.norm_eq, EuclideanSpace.norm_eq ]

  have h_norm_sq : (A.val.mulVec v) ⬝ᵥ (A.val.mulVec v) = v ⬝ᵥ v := by
    simp_all [ Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
    erw [ A.2.1 ]
    norm_num

  have h_norm_sq : ∑ i, (A.val.mulVec v i) ^ 2 = ∑ i, (v i) ^ 2 := by
    simp only [ sq  ]
    exact h_norm_sq

  simp_all [ Matrix.mulVec, dotProduct ]
  exact congrArg Real.sqrt h_norm_sq

noncomputable def multiplication {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ) : RealIsometry n where
  toFun x := A • x
  is_isometry x y := by
    rw [← smul_sub]
    apply norm_orthogonal
  surjective := by
    intro y
    use A⁻¹ • y
    simp

/-
Lemma 1.4 If f and g are isometries, so is f ∘ g.
-/
def RealIsometry.comp {n : ℕ} (f : RealIsometry n) (g : RealIsometry n) : RealIsometry n where
  toFun := f.toFun ∘ g.toFun
  is_isometry x y := by
    have := calc
      ‖x - y‖ = ‖g.toFun x - g.toFun y‖ := by rw [g.is_isometry]
      _ = ‖f.toFun (g.toFun x) - f.toFun (g.toFun y)‖ := by rw [f.is_isometry]
      _ = ‖(f.toFun ∘ g.toFun) x - (f.toFun ∘ g.toFun) y‖ := by congr
    exact Eq.symm this
  surjective := by
    grind [Function.Surjective.comp]

/-
Prerequisites for the "important consequence"
-/
instance RealIsometry.instOne {n : ℕ} : One (RealIsometry n) where one := RealIsometry.identity
instance RealIsometry.instMul {n : ℕ} : Mul (RealIsometry n) where mul a b := RealIsometry.comp a b
instance RealIsometry.instMonoid {n : ℕ} : Monoid (RealIsometry n) where
  mul a b := RealIsometry.comp a b
  mul_assoc a b c := by rfl
  one_mul a := by rfl
  mul_one a := by rfl

noncomputable instance {n : ℕ} : Inv (RealIsometry n) where inv := RealIsometry.inverse

/-
Important consequence: The set of all isometries of Rⁿ, denoted by I(Rⁿ),
forms a group.
-/
noncomputable instance RealIsometry.instGroup {n : ℕ} : Group (RealIsometry n) := Group.ofLeftAxioms
  (fun _ _ _ => rfl) (fun _ => rfl) (fun a => by
    ext x : 2
    exact congr_fun (Function.invFun_comp a.injective) x)

noncomputable def standardForm {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)) : RealIsometry n where
  toFun x := A • x + b
  is_isometry x y := calc
    ‖A • x + b - (A • y + b)‖ = ‖A • (x - y)‖ := by congr 1 ; grind [smul_sub]
    _ = ‖x - y‖ := by apply norm_orthogonal
  surjective := fun y => ⟨ A⁻¹ • (y - b), by simp ⟩

/-
Theorem 1.5 Every real isometry is of the form x ↦ Ax + b
-/
theorem exists_mul {n : ℕ} (a : RealIsometry n)
: ∃ O : Matrix.orthogonalGroup (Fin n) ℝ, ∃ b : EuclideanSpace ℝ (Fin n), a.toFun = (standardForm O b).toFun := by
  sorry

theorem exists_mul_unique {n : ℕ} (a : RealIsometry n)
: ∃! (p : Matrix.orthogonalGroup (Fin n) ℝ × EuclideanSpace ℝ (Fin n)), a.toFun = (standardForm p.1 p.2).toFun := by
  sorry

/-
Example 1.2a: translations
-/

noncomputable def RealIsometry.translation {n : ℕ} (d : EuclideanSpace ℝ (Fin n)) : RealIsometry n where
  toFun x := x + d
  is_isometry x y := by
    abel_nf
  surjective := fun x => by
    use x - d
    simp

lemma one_eq {n : ℕ} : (1 : RealIsometry n) = RealIsometry.identity := rfl

lemma mul_eq {n : ℕ} (a b : RealIsometry n) : (a * b) = RealIsometry.comp a b := rfl

lemma inv_eq {n : ℕ} (a : RealIsometry n) : a⁻¹ = RealIsometry.inverse a := rfl

lemma my_lemma (G : Type*) [Group G] (a b : G) : a = b⁻¹ ↔ a * b = 1 := eq_inv_iff_mul_eq_one

/-
The translation subgroup. Auslander and Cook, An Algebraic Classification of the Three-Dimensional Crystallographic Groups.
-/
def RealIsometry.translationSubgroup {n : ℕ} : Subgroup (RealIsometry n) where
  carrier := { RealIsometry.translation d | d : EuclideanSpace ℝ (Fin n) }
  mul_mem' := by
    intro a b ha hb
    simp_all
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    use a' + b'
    ext v : 2
    simp [RealIsometry.translation, mul_eq, RealIsometry.comp]
    grind
  one_mem' := by
    use 0
    simp [RealIsometry.translation, one_eq, RealIsometry.identity]
    grind
  inv_mem' := by
    intro a ha
    obtain ⟨a', rfl⟩ := ha
    use -a'
    rw [eq_inv_iff_mul_eq_one]
    ext v : 2
    simp [RealIsometry.translation, mul_eq, RealIsometry.comp, one_eq, RealIsometry.identity]

instance {n : ℕ} : (RealIsometry.translationSubgroup (n := n)).Normal := by
  constructor
  intro a ha g
  simp only [RealIsometry.translationSubgroup, Subgroup.mem_mk] at *
  obtain ⟨d, rfl⟩ := ha
  obtain ⟨O, b, hg⟩ := exists_mul g
  use g.toFun d - g.toFun 0
  -- g(y) = O • y + b for all y
  have hgf : ∀ y, g.toFun y = (standardForm O b).toFun y := congr_fun hg
  simp only [standardForm] at hgf
  -- g(g⁻¹(x)) = x for all x
  have hcancel : ∀ x, g.toFun (g⁻¹.toFun x) = x := fun x =>
    congr_fun (congr_arg RealIsometry.toFun (mul_inv_cancel g)) x
  ext x : 2
  simp only [mul_eq, RealIsometry.comp, Function.comp, RealIsometry.translation]
  -- Goal: g.toFun (g⁻¹.toFun x + d) = x + (g.toFun d - g.toFun 0)
  -- Simplify RHS: g(d) - g(0) = (O•d + b) - (O•0 + b) = O•d
  have hRHS : g.toFun d - g.toFun 0 = O • d := by
    rw [hgf d, hgf 0]; simp [smul_zero]
  rw [hRHS]
  -- Goal: g.toFun (g⁻¹.toFun x + d) = x + O • d
  -- Expand LHS using standard form
  rw [hgf, smul_add]
  -- Goal: O • g⁻¹.toFun x + O • d + b = x + O • d
  -- Use hcancel: g(g⁻¹(x)) = O • g⁻¹(x) + b = x
  have hc : O • g⁻¹.toFun x + b = x := by rw [← hgf]; exact hcancel x
  -- Rearrange and substitute
  have : O • g⁻¹.toFun x + O • d + b = (O • g⁻¹.toFun x + b) + O • d := by abel
  rw [this, hc]

/-
The subgroup that fixes the origin.
-/
def RealIsometry.rotationSubgroup {n : ℕ} : Subgroup (RealIsometry n) where
  carrier := { r | r.toFun 0 = 0 }
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    change (a * b).toFun 0 = 0
    simp only [mul_eq, RealIsometry.comp, Function.comp]
    rw [hb, ha]
  one_mem' := by
    simp [one_eq, RealIsometry.identity]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : a.toFun (a⁻¹.toFun 0) = 0 := by
      have : (a * a⁻¹).toFun 0 = (1 : RealIsometry _).toFun 0 := by
        rw [mul_inv_cancel]
      simp only [mul_eq, RealIsometry.comp, Function.comp, one_eq, RealIsometry.identity] at this
      simpa using this
    exact a.injective (by rw [h1, ha])

-- standardForm is the product of a translation and a multiplication
lemma standardForm_eq_mul {n : ℕ} (A : Matrix.orthogonalGroup (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)) :
    standardForm A b = RealIsometry.translation b * multiplication A := by
  ext x : 2
  simp [standardForm, RealIsometry.translation, multiplication, mul_eq, RealIsometry.comp, Function.comp]

-- multiplication is in the rotation subgroup (fixes the origin)
lemma multiplication_mem_rotationSubgroup {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    multiplication O ∈ RealIsometry.rotationSubgroup := by
  change (multiplication O).toFun 0 = 0
  simp [multiplication, smul_zero]

-- Every element of rotationSubgroup is a multiplication
lemma mem_rotationSubgroup_exists_multiplication {n : ℕ} {r : RealIsometry n}
    (hr : r ∈ RealIsometry.rotationSubgroup) :
    ∃ O : Matrix.orthogonalGroup (Fin n) ℝ, r = multiplication O := by
  obtain ⟨O, b, h⟩ := exists_mul r
  have h0 : r.toFun 0 = 0 := hr
  have hb : b = 0 := by
    have : (standardForm O b).toFun 0 = 0 := by rw [← congr_fun h]; exact h0
    simp [standardForm, smul_zero] at this
    exact this
  subst hb
  refine ⟨O, ?_⟩
  ext x : 2
  have : r.toFun x = (standardForm O 0).toFun x := congr_fun h x
  simp [standardForm, multiplication] at this ⊢
  exact this

-- translationSubgroup and rotationSubgroup are disjoint
lemma disjoint_translation_rotation {n : ℕ} :
    Disjoint (RealIsometry.translationSubgroup (n := n)) RealIsometry.rotationSubgroup := by
  rw [Subgroup.disjoint_def]
  intro g hg hr
  simp only [RealIsometry.translationSubgroup, Subgroup.mem_mk] at hg
  obtain ⟨d, rfl⟩ := hg
  simp only [RealIsometry.rotationSubgroup, Subgroup.mem_mk] at hr
  have : d = 0 := by simpa [RealIsometry.translation] using hr
  subst this
  ext x : 2
  simp [RealIsometry.translation, one_eq, RealIsometry.identity]

-- translationSubgroup * rotationSubgroup = univ
lemma mul_eq_univ_translation_rotation {n : ℕ} :
    ((RealIsometry.translationSubgroup : Subgroup (RealIsometry n)) : Set (RealIsometry n)) * ((RealIsometry.rotationSubgroup : Subgroup (RealIsometry n)) : Set (RealIsometry n)) = Set.univ := by
  ext g
  simp only [Set.mem_univ, iff_true]
  obtain ⟨O, b, h⟩ := exists_mul g
  refine ⟨RealIsometry.translation b, ⟨b, rfl⟩, multiplication O, multiplication_mem_rotationSubgroup O, ?_⟩
  change RealIsometry.translation b * multiplication O = g
  rw [← standardForm_eq_mul]
  ext x : 2
  exact (congr_fun h x).symm

-- translationSubgroup and rotationSubgroup are complementary
lemma isComplement'_translation_rotation {n : ℕ} :
    (RealIsometry.translationSubgroup (n := n)).IsComplement' RealIsometry.rotationSubgroup :=
  Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    disjoint_translation_rotation mul_eq_univ_translation_rotation

-- RealIsometry is isomorphic to the semidirect product of translations and rotations
noncomputable def realIsometry_semidirectProduct {n : ℕ} :=
  SemidirectProduct.mulEquivSubgroup (isComplement'_translation_rotation (n := n))
