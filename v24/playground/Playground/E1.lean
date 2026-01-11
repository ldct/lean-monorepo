import Mathlib

/-
Exceptional isometries of R^3
-/

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
Definition 1 (page 2)
-/
@[ext, grind ext]
structure RealIsometry where
  f : R3  → R3
  is_isometry : ∀ x y, ‖f x - f y‖ = ‖x - y‖
  surjective : Function.Surjective f


def RealIsometry.identity : RealIsometry where
  f := id
  is_isometry := by grind
  surjective := Function.surjective_id

noncomputable def translation (d : R3) : RealIsometry where
  f x := x + d
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
  f x := A • x
  is_isometry x y := by
    rw [← smul_sub]
    apply norm_orthogonal
  surjective := by
    intro y
    use A⁻¹ • y
    simp

theorem RealIsometry.injective (f : RealIsometry) : Function.Injective f.f := by
  intro x y hxy
  have h1 : ‖x - y‖ = ‖f.f x - f.f y‖ := by
    rw [f.is_isometry]
  have h2 : f.f x - f.f y = 0 := sub_eq_zero_of_eq hxy
  rw [h2] at h1
  simp at h1
  grind

#check Function.invFun

theorem RealIsometry.bijective (f : RealIsometry) : Function.Bijective f.f := by
  constructor
  · exact injective f
  · exact f.surjective

example (A B : Type) [Nonempty A] (f : A → B) (h : Function.Bijective f) : Function.Surjective f.invFun := by
  exact Function.invFun_surjective h.injective

theorem invFun_surjective (T : Type) [Nonempty T] (f : T → T) (hf : Function.Injective f) : Function.Surjective (Function.invFun f) := by
  exact (Function.leftInverse_invFun hf).surjective

theorem invFun_injective (T : Type) [Nonempty T] (f : T → T) (hf : Function.Surjective f) : Function.Injective (Function.invFun f) := by
  exact (Function.rightInverse_invFun hf).injective

noncomputable def RealIsometry.inverse (f : RealIsometry) : RealIsometry where
  f :=  f.f.invFun
  is_isometry x y := by
    rw [← f.is_isometry]
    have := @Function.rightInverse_invFun _ _ _ f.f f.surjective
    unfold Function.RightInverse at this
    unfold Function.LeftInverse at this
    simp [this]
  surjective := by
    apply Function.invFun_surjective
    exact injective f


def RealIsometry.comp (a : RealIsometry) (b : RealIsometry) : RealIsometry where
  f := a.f ∘ b.f
  is_isometry x y := by
    -- Apply the isometry property of $b$ first, then apply the isometry property of $a$.
    have h_comp : ‖a.f (b.f x) - a.f (b.f y)‖ = ‖b.f x - b.f y‖ := by
      -- Apply the isometry property of $a$ to the points $b.f x$ and $b.f y$.
      apply a.is_isometry;
    -- Apply the isometry property of $b$ to conclude the proof.
    have := b.is_isometry x y; aesop
  surjective := by
    -- Since $a$ and $b$ are both surjective, their composition $a \circ b$ is also surjective.
    apply Function.Surjective.comp a.surjective b.surjective

noncomputable def standardForm (A : O3) (b : R3): RealIsometry where
  f x := A • x + b
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
    -- By definition of matrix multiplication and vector addition, we can simplify the expression.
    simp

-- Every real isometry is of the form x ↦ Ax + b
theorem exists_mul (a : RealIsometry)
: ∃ O : O3, ∃ b : R3, a.f = (standardForm O b).f := by
  -- By definition of $a$, we know that $a$ is an isometry, so $a.f$ is an affine transformation.
  have h_affine : ∃ (A : O3) (b : R3), ∀ x, a.f x = A • x + b := by
    set T := a.f 0
    set S : RealIsometry := ⟨fun x => a.f x - T, by
      exact fun x y => by rw [ ← a.is_isometry x y ] ; simp +decide [ sub_sub_sub_cancel_right ] ;, by
      exact fun x => by cases' a.surjective ( x + T ) with y hy; use y; aesop;⟩
    generalize_proofs at *;
    -- Since $S$ is an isometry, it preserves the inner product.
    have h_inner : ∀ x y : R3, inner ℝ (S.f x) (S.f y) = inner ℝ x y := by
      intro x y
      have h_norm_sq : ‖S.f x‖^2 = ‖x‖^2 ∧ ‖S.f y‖^2 = ‖y‖^2 ∧ ‖S.f x - S.f y‖^2 = ‖x - y‖^2 := by
        have := S.is_isometry x 0; have := S.is_isometry y 0; have := S.is_isometry x y; aesop;
      norm_num [ @norm_sub_sq ℝ ] at *;
      grind;
    -- Since $S$ is an isometry, it is linear.
    have h_linear : ∀ x y : R3, S.f (x + y) = S.f x + S.f y := by
      -- By definition of $S$, we know that $S(x + y) = S(x) + S(y)$ for all $x, y \in \mathbb{R}^3$.
      intros x y
      have h_eq : ‖S.f (x + y) - (S.f x + S.f y)‖^2 = 0 := by
        rw [ @norm_sub_sq ℝ ];
        simp_all +decide [ norm_add_sq_real, inner_add_right, inner_add_left ];
        simp_all +decide [ ← real_inner_self_eq_norm_sq ];
        rw [ inner_add_add_self ] ; ring;
        rw [ real_inner_comm, sub_self ];
      exact sub_eq_zero.mp ( norm_eq_zero.mp ( sq_eq_zero_iff.mp h_eq ) );
    -- Since $S$ is linear, it is represented by a matrix $A$.
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 3) (Fin 3) ℝ, ∀ x : R3, S.f x = A.mulVec x := by
      have h_linear : ∃ A : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ), ∀ x : R3, S.f x = A x := by
        have h_linear : ∀ x : R3, ∀ c : ℝ, S.f (c • x) = c • S.f x := by
          intro x c; have := h_inner ( c • x ) ( c • x ) ; simp_all +decide [ inner_self_eq_norm_sq_to_K ] ;
          have h_inner : ∀ x y : R3, inner ℝ (S.f (c • x) - c • S.f x) (S.f (c • x) - c • S.f x) = 0 := by
            simp_all +decide [ inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ];
          exact sub_eq_zero.mp ( by simpa [ inner_self_eq_norm_sq_to_K ] using h_inner x x );
        exact ⟨ { toFun := S.f, map_add' := by aesop, map_smul' := by aesop }, fun x => rfl ⟩;
      obtain ⟨ A, hA ⟩ := h_linear;
      use LinearMap.toMatrix' A;
      simp +decide [ hA, Matrix.mulVec, dotProduct ];
    -- Since $S$ is an isometry, $A$ must be orthogonal.
    have h_orthogonal : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
      simp_all +decide [ Matrix.mulVec, dotProduct ];
      have h_orthogonal : A.transpose * A = 1 := by
        ext i j; specialize h_inner ( Pi.single i 1 ) ( Pi.single j 1 ) ; simp_all +decide [ Matrix.mul_apply, dotProduct ] ;
        simp_all +decide [ Fin.sum_univ_three, Matrix.one_apply, inner ];
        fin_cases i <;> fin_cases j <;> simp +decide [ Pi.single_apply ] at h_inner ⊢ <;> linarith!;
      exact ⟨ h_orthogonal, Matrix.mul_eq_one_comm.mp h_orthogonal ⟩;
    use ⟨ A, h_orthogonal ⟩, T;
    intro x; specialize hA x; rw [ sub_eq_iff_eq_add ] at hA; aesop;
  exact ⟨ h_affine.choose, h_affine.choose_spec.choose, funext h_affine.choose_spec.choose_spec ⟩

instance RealIsometry.instOne : One RealIsometry where
  one := RealIsometry.identity

instance RealIsometry.instMul : Mul RealIsometry where
  mul a b := RealIsometry.comp a b

instance RealIsometry.instMonoid : Monoid RealIsometry where
  mul a b := RealIsometry.comp a b
  mul_assoc a b c := by rfl
  one_mul a := by rfl
  mul_one a := by rfl

noncomputable instance : Inv RealIsometry where
  inv := RealIsometry.inverse

noncomputable instance RealIsometry.instGroup : Group RealIsometry := Group.ofLeftAxioms
  (by
    intro a b c
    rfl
  )
  (by
    intro a
    rfl
  )
  (by
    intro a
    have : a⁻¹ * a = comp (inverse a) a := by rfl
    rw [this]
    have : 1 = identity := by rfl
    rw [this]
    ext x i
    simp [comp, inverse, identity ]
    revert i
    rw [← funext_iff]
    revert x
    rw [← funext_iff]
    have : (fun x ↦ Function.invFun a.f (a.f x)) = (a.f.invFun) ∘ a.f := by grind
    nth_rw 1 [this]
    exact Function.invFun_comp a.injective
  )

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

def IsExceptional (H : Subgroup RealIsometry) : Prop :=
  ¬ IsCyclic H ∧ ¬ IsDihedral H ∧ Nat.card H ≠ 0

theorem RealIsometry.existsExceptional (n : ℕ) [NeZero n]
: ∃ f : Subgroup RealIsometry, IsExceptional f := by
  sorry
