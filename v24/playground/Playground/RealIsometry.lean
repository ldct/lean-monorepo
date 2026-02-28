import Mathlib

set_option linter.style.longLine false

attribute [grind =] abs_eq_abs
attribute [grind =] lt_abs
attribute [grind =] abs_lt

attribute [grind] max_comm
attribute [grind] max_self
attribute [grind] max_assoc

@[grind =]
theorem abs_eq_max (a : ℝ) : |a| = max a (-a) := by rfl

example (a b : ℝ) : max a b = max b a := by grind
example (a : ℝ) : max a a = a := by grind
example (a b c : ℝ) : max a (max b c) = max (max c a) b := by grind
example (a : ℝ) : |a| = max a (-a) := by grind
example (a : ℝ) : max a (-a) = max (-a) a := by grind
example (a : ℝ) : a = - (-a) := by grind
example (a : ℝ) : |a| = |-a| := by grind

example (a b c : ℝ) : |a + b - c| = |c - a - b| := by grind
example (a b c : ℝ) (h1 : |a - b| < 1) (h2 : |a - c| < 1) (h3 : 100 < |b - c|) : False := by grind


theorem abs_lt' (a b : ℝ) : |a| < b ↔ a < b ∧ -a < b := by
  grind

macro "absarith" : tactic => `(tactic|
  (try repeat rw [abs_lt'] at *;
   try repeat rw [lt_div_iff₀ (by assumption)] at *;
   constructor <;>
   nlinarith (config := {splitHypotheses := true})))

variable (f : ℝ → ℝ) (t c ε y : ℝ) (hc : 0 < c) (hε : 0 < ε) in
example (h : |f y - f t| < ε / c) :
    |c * f y - c * f t| < ε := by
  absarith

#check EuclideanSpace

abbrev MAT := Matrix (Fin 3) (Fin 3) ℝ
abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev O3 := Matrix.orthogonalGroup (Fin 3) ℝ

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

example (A B : Type) [Nonempty A] (f : A → B) (h : Function.Bijective f) : Function.Surjective f.invFun := by
  grind [Function.invFun_surjective, Function.Bijective]

theorem invFun_surjective (T : Type) [Nonempty T] (f : T → T) (hf : Function.Injective f) : Function.Surjective (Function.invFun f) := by
  have h1 := Function.leftInverse_invFun hf
  grind [Function.leftInverse_invFun, Function.LeftInverse.surjective, Function.leftInverse_invFun]

theorem invFun_injective (T : Type) [Nonempty T] (f : T → T) (hf : Function.Surjective f) : Function.Injective (Function.invFun f) := by
  exact (Function.rightInverse_invFun hf).injective

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

noncomputable def translation (d : R3) : RealIsometry where
  toFun x := x + d
  is_isometry x y := by
    abel_nf
  surjective := fun x => by
    use x - d
    simp

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
  is_isometry x y := by
    -- Since $A$ is orthogonal, we have $\|A \cdot (x - y)\| = \|x - y\|$.
    have h_norm : ‖A.val • (x - y)‖ = ‖x - y‖ := by
      -- Since $A$ is orthogonal, we have $\|A \cdot (x - y)\| = \|x - y\|$ by the properties of orthogonal matrices.
      apply norm_orthogonal;
    -- Since $A$ is orthogonal, we have $\|A \cdot (x - y)\| = \|x - y\|$. Therefore, the norm of $(A • x + b) - (A • y + b)$ is equal to the norm of $x - y$.
    have h_norm : ‖(A.val • x + b) - (A.val • y + b)‖ = ‖A.val • (x - y)‖ := by
      rw [ smul_sub ] ; abel_nf;
    exact h_norm.trans ‹_›
  surjective := by
    -- To prove surjectivity, take any y in R3. We need to find an x such that A • x + b = y.
    intro y
    use A⁻¹ • (y - b);
    simp

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
  generalize_proofs at *
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
    norm_num [@norm_sub_sq ℝ] at *; grind
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

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)
def IsCyclicOfOrder (n : ℕ) (G : Type*) [Group G] : Prop :=
  IsCyclic G ∧ Nat.card G = n
