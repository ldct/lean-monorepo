import Mathlib

set_option linter.style.longLine false
open scoped Pointwise

-- #check EuclideanSpace

abbrev MAT := Matrix (Fin 3) (Fin 3) ℝ
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
structure RealIsometry where
  toFun : R3  → R3
  is_isometry : ∀ x y, ‖toFun x - toFun y‖ = ‖x - y‖
  surjective : Function.Surjective toFun


/-
Lemma 1.2. Every isometry is injective.
-/
@[grind] theorem RealIsometry.injective (f : RealIsometry) : Function.Injective f.toFun := by
  intro x y hxy
  have := calc
    0 = ‖f.toFun x - f.toFun y‖ := by grind [norm_eq_zero]
    _ = ‖x - y‖ := by rw [f.is_isometry]
  grind [norm_eq_zero]

/-
Prerequisite for lemma 1.3 If f is an isometry, then f⁻¹ exists.
-/
theorem RealIsometry.bijective (f : RealIsometry) : Function.Bijective f.toFun := by grind [Function.Bijective]

/-
Lemma 1.3 If f is an isometry, so is f⁻¹.
-/
noncomputable def RealIsometry.inverse (f : RealIsometry) : RealIsometry where
  toFun := f.toFun.invFun
  is_isometry x y := by
    rw [← f.is_isometry]
    have := Function.rightInverse_invFun f.surjective
    unfold Function.RightInverse at this
    unfold Function.LeftInverse at this
    simp [this]
  surjective := by
    grind [Function.invFun_surjective]


def RealIsometry.identity : RealIsometry where
  toFun := id
  is_isometry := by grind
  surjective := Function.surjective_id

example (v : R3) : ‖v‖^2 = v ⬝ᵥ v := by
  simp [EuclideanSpace.norm_sq_eq];
  simp [dotProduct];
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

noncomputable def multiplication (A : O3) : RealIsometry where
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
def RealIsometry.comp (f : RealIsometry) (g : RealIsometry) : RealIsometry where
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
instance RealIsometry.instOne : One RealIsometry where one := RealIsometry.identity
instance RealIsometry.instMul : Mul RealIsometry where mul a b := RealIsometry.comp a b
instance RealIsometry.instMonoid : Monoid RealIsometry where
  mul a b := RealIsometry.comp a b
  mul_assoc a b c := by rfl
  one_mul a := by rfl
  mul_one a := by rfl

noncomputable instance : Inv RealIsometry where inv := RealIsometry.inverse

/-
Important consequence: The set of all isometries of Rⁿ, denoted by I(Rⁿ),
forms a group.
-/
noncomputable instance RealIsometry.instGroup : Group RealIsometry := Group.ofLeftAxioms
  (fun _ _ _ => rfl) (fun _ => rfl) (fun a => by
    ext x : 2
    exact congr_fun (Function.invFun_comp a.injective) x)

noncomputable def standardForm (A : O3) (b : R3) : RealIsometry where
  toFun x := A • x + b
  is_isometry x y := calc
    ‖A • x + b - (A • y + b)‖ = ‖A • (x - y)‖ := by congr 1 ; grind [smul_sub]
    _ = ‖x - y‖ := by apply norm_orthogonal
  surjective := fun y => ⟨ A⁻¹ • (y - b), by simp ⟩

/-
Theorem 1.5 Every real isometry is of the form x ↦ Ax + b
-/
theorem exists_mul (a : RealIsometry)
: ∃ O : O3, ∃ b : R3, a.toFun = (standardForm O b).toFun := by
  -- Step 1: Define b = a(0) and the origin-fixing isometry S(x) = a(x) - b
  set b := a.toFun 0
  set S : RealIsometry := ⟨fun x => a.toFun x - b, by
    intro x y; change ‖(a.toFun x - b) - (a.toFun y - b)‖ = ‖x - y‖
    rw [sub_sub_sub_cancel_right]; exact a.is_isometry x y, by
    intro x; obtain ⟨y, hy⟩ := a.surjective (x + b)
    exact ⟨y, by change a.toFun y - b = x; simp [hy]⟩⟩
  -- Step 2: S preserves inner products (via polarization)
  have hSinner : ∀ x y : R3, inner ℝ (S.toFun x) (S.toFun y) = inner ℝ x y := by
    intro x y
    -- First establish that S preserves norms (using S(0) = 0)
    have hSx : ‖S.toFun x‖^2 = ‖x‖^2 := by
      have := S.is_isometry x 0; aesop
    have hSy : ‖S.toFun y‖^2 = ‖y‖^2 := by
      have := S.is_isometry y 0; aesop
    have hSxy : ‖S.toFun x - S.toFun y‖^2 = ‖x - y‖^2 := by
      have := S.is_isometry x y; aesop
    -- Apply the polarization identity: 2⟨u,v⟩ = ‖u‖² + ‖v‖² - ‖u-v‖²
    norm_num [@norm_sub_sq ℝ] at *
    grind
  -- Step 3: S is additive
  have hSadd : ∀ x y : R3, S.toFun (x + y) = S.toFun x + S.toFun y := by
    intro x y
    -- Show ‖S(x+y) - (S(x) + S(y))‖² = 0
    suffices h : ‖S.toFun (x + y) - (S.toFun x + S.toFun y)‖^2 = 0 by
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h))
    rw [@norm_sub_sq ℝ]
    simp_all [norm_add_sq_real, inner_add_right, inner_add_left]
    simp_all [← real_inner_self_eq_norm_sq]
    rw [inner_add_add_self]; ring_nf; rw [real_inner_comm, sub_self]
  -- Step 4: S is scalar-homogeneous
  have hSsmul : ∀ (c : ℝ) (x : R3), S.toFun (c • x) = c • S.toFun x := by
    intro c x
    -- Show ⟨S(cx) - cS(x), S(cx) - cS(x)⟩ = 0
    have := hSinner (c • x) (c • x); simp_all [inner_self_eq_norm_sq_to_K]
    have hzero : ∀ u v : R3, inner ℝ (S.toFun (c • x) - c • S.toFun x) (S.toFun (c • x) - c • S.toFun x) = 0 := by
      simp_all [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    exact sub_eq_zero.mp (by simpa [inner_self_eq_norm_sq_to_K] using hzero x x)
  -- Step 5: Extract the matrix representation
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) ℝ, ∀ x : R3, S.toFun x = M.mulVec x := by
    have ⟨L, hL⟩ : ∃ L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ), ∀ x : R3, S.toFun x = L x :=
      ⟨{ toFun := S.toFun, map_add' := by aesop, map_smul' := by aesop }, fun _ => rfl⟩
    exact ⟨LinearMap.toMatrix' L, by simp [hL]⟩
  -- Step 6: M is orthogonal (MᵀM = I)
  have hMorth : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    simp_all
    have hort : M.transpose * M = 1 := by
      ext i j; specialize hSinner (Pi.single i 1) (Pi.single j 1); simp_all [Matrix.mul_apply]
      simp_all [Fin.sum_univ_three, Matrix.one_apply, inner]
      fin_cases i <;> fin_cases j <;> simp at hSinner ⊢ <;> linarith!
    exact ⟨hort, Matrix.mul_eq_one_comm.mp hort⟩
  -- Step 7: Combine: a(x) = M•x + b
  exact ⟨⟨M, hMorth⟩, b, funext fun x => by
    have := hM x; rw [sub_eq_iff_eq_add] at this; aesop⟩

theorem exists_mul_unique (a : RealIsometry)
: ∃! (p : O3 × R3), a.toFun = (standardForm p.1 p.2).toFun := by
  obtain ⟨O, b, h⟩ := exists_mul a
  refine ⟨⟨O, b⟩, h, ?_⟩
  rintro ⟨O', b'⟩ h'
  have heq : ∀ x, (standardForm O' b').toFun x = (standardForm O b).toFun x :=
    congr_fun (h'.symm.trans h)
  simp only [standardForm] at heq
  have hb : b' = b := by have := heq 0; grind [smul_zero, zero_add]
  subst hb
  have hsmul : ∀ x : R3, (O' : MAT) • x = (O : MAT) • x :=
    fun x => add_right_cancel (heq x)
  refine Prod.ext ?_ rfl
  -- Goal: O' = O
  have hmat : (O' : MAT) = (O : MAT) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    have := hsmul (Pi.single j 1)
    exact this
  grind

/-
Example 1.2a: translations
-/

noncomputable def translation (d : R3) : RealIsometry where
  toFun x := x + d
  is_isometry x y := by
    abel_nf
  surjective := fun x => by
    use x - d
    simp

lemma one_eq : (1 : RealIsometry) = RealIsometry.identity := rfl

lemma mul_eq (a b : RealIsometry) : (a * b) = RealIsometry.comp a b := rfl

lemma inv_eq (a : RealIsometry) : a⁻¹ = RealIsometry.inverse a := rfl

lemma my_lemma (G : Type*) [Group G] (a b : G) : a = b⁻¹ ↔ a * b = 1 := eq_inv_iff_mul_eq_one

/-
The translation subgroup. Auslander and Cook, An Algebraic Classification of the Three-Dimensional Crystallographic Groups.
-/
def RealIsometry.translationSubgroup : Subgroup RealIsometry where
  carrier := { translation d | d : R3 }
  mul_mem' := by
    intro a b ha hb
    simp_all
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    use a' + b'
    ext v : 2
    simp [translation, mul_eq, RealIsometry.comp]
    grind
  one_mem' := by
    use 0
    simp [translation, one_eq, RealIsometry.identity]
    grind
  inv_mem' := by
    intro a ha
    obtain ⟨a', rfl⟩ := ha
    use -a'
    rw [eq_inv_iff_mul_eq_one]
    ext v : 2
    simp [translation, mul_eq, RealIsometry.comp, one_eq, RealIsometry.identity]

instance : RealIsometry.translationSubgroup.Normal := by
  constructor
  intro n hn g
  simp only [RealIsometry.translationSubgroup, Subgroup.mem_mk] at *
  obtain ⟨d, rfl⟩ := hn
  obtain ⟨O, b, hg⟩ := exists_mul g
  use g.toFun d - g.toFun 0
  -- g(y) = O • y + b for all y
  have hgf : ∀ y, g.toFun y = (standardForm O b).toFun y := congr_fun hg
  simp only [standardForm] at hgf
  -- g(g⁻¹(x)) = x for all x
  have hcancel : ∀ x, g.toFun (g⁻¹.toFun x) = x := fun x =>
    congr_fun (congr_arg RealIsometry.toFun (mul_inv_cancel g)) x
  ext x : 2
  simp only [mul_eq, RealIsometry.comp, Function.comp, translation]
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
def RealIsometry.rotationSubgroup : Subgroup RealIsometry where
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
      have : (a * a⁻¹).toFun 0 = (1 : RealIsometry).toFun 0 := by
        rw [mul_inv_cancel]
      simp only [mul_eq, RealIsometry.comp, Function.comp, one_eq, RealIsometry.identity] at this
      simpa using this
    exact a.injective (by rw [h1, ha])

-- standardForm is the product of a translation and a multiplication
lemma standardForm_eq_mul (A : O3) (b : R3) :
    standardForm A b = translation b * multiplication A := by
  ext x : 2
  simp [standardForm, translation, multiplication, mul_eq, RealIsometry.comp, Function.comp]

-- multiplication is in the rotation subgroup (fixes the origin)
lemma multiplication_mem_rotationSubgroup (O : O3) :
    multiplication O ∈ RealIsometry.rotationSubgroup := by
  change (multiplication O).toFun 0 = 0
  simp [multiplication, smul_zero]

-- Every element of rotationSubgroup is a multiplication
lemma mem_rotationSubgroup_exists_multiplication {r : RealIsometry}
    (hr : r ∈ RealIsometry.rotationSubgroup) :
    ∃ O : O3, r = multiplication O := by
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
lemma disjoint_translation_rotation :
    Disjoint RealIsometry.translationSubgroup RealIsometry.rotationSubgroup := by
  rw [Subgroup.disjoint_def]
  intro g hg hr
  simp only [RealIsometry.translationSubgroup, Subgroup.mem_mk] at hg
  obtain ⟨d, rfl⟩ := hg
  simp only [RealIsometry.rotationSubgroup, Subgroup.mem_mk] at hr
  have : d = 0 := by simpa [translation] using hr
  subst this
  ext x : 2
  simp [translation, one_eq, RealIsometry.identity]

-- translationSubgroup * rotationSubgroup = univ
lemma mul_eq_univ_translation_rotation :
    (RealIsometry.translationSubgroup : Set RealIsometry) * RealIsometry.rotationSubgroup = (Set.univ : Set RealIsometry) := by
  ext g
  simp only [Set.mem_univ, iff_true]
  obtain ⟨O, b, h⟩ := exists_mul g
  refine ⟨translation b, ⟨b, rfl⟩, multiplication O, multiplication_mem_rotationSubgroup O, ?_⟩
  change translation b * multiplication O = g
  rw [← standardForm_eq_mul]
  ext x : 2
  exact (congr_fun h x).symm

-- translationSubgroup and rotationSubgroup are complementary
lemma isComplement'_translation_rotation :
    RealIsometry.translationSubgroup.IsComplement' RealIsometry.rotationSubgroup :=
  Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    disjoint_translation_rotation mul_eq_univ_translation_rotation

-- RealIsometry is isomorphic to the semidirect product of translations and rotations
noncomputable def realIsometry_semidirectProduct :=
  SemidirectProduct.mulEquivSubgroup isComplement'_translation_rotation
