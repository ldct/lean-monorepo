import Playground.RealIsometry.Basic

-- chapter 1.2: Classification of isometries of R^2

#check RealIsometry.translation

#check PlaneIsometry


abbrev MAT2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev R2 := EuclideanSpace ℝ (Fin 2)
abbrev O2 := Matrix.orthogonalGroup (Fin 2) ℝ

/-
Example 1.2a: translations
-/
noncomputable def PlaneIsometry.translation (a : R2)
: PlaneIsometry := @RealIsometry.translation 2 a

/-
Example 1.2b: rotation about the origin by an angle α
-/
private noncomputable def rotMat (α : ℝ) : MAT2 :=
  !![Real.cos α, -Real.sin α; Real.sin α, Real.cos α]

private lemma rotMat_orthogonal (α : ℝ) : rotMat α ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  have hRT : Matrix.transpose (rotMat α) * rotMat α = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotMat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;>
      ring_nf <;> simp [Real.sin_sq_add_cos_sq, Real.cos_sq_add_sin_sq]
  exact ⟨hRT, Matrix.mul_eq_one_comm.mp hRT⟩

private noncomputable def rotO2 (α : ℝ) : O2 := ⟨rotMat α, rotMat_orthogonal α⟩

noncomputable def PlaneIsometry.r0 (α : ℝ) : PlaneIsometry where
  toFun x := !![Real.cos α, -Real.sin α; Real.sin α, Real.cos α]  • x
  is_isometry x y := by
    show ‖(rotMat α) • x - (rotMat α) • y‖ = ‖x - y‖
    rw [← smul_sub]
    exact norm_orthogonal 2 (rotO2 α) (x - y)
  surjective := (multiplication (rotO2 α)).surjective

/-
Example 1.2c: rotation about a general point z by an angle α
-/
noncomputable def PlaneIsometry.rotation (z : R2) (α : ℝ) : PlaneIsometry where
  toFun x := !![Real.cos α, -Real.sin α; Real.sin α, Real.cos α]  • (x - z) + z
  is_isometry x y := by
    show ‖(rotMat α) • (x - z) + z - ((rotMat α) • (y - z) + z)‖ = ‖x - y‖
    have heq : (rotMat α) • (x - z) + z - ((rotMat α) • (y - z) + z) = (rotMat α) • (x - y) := by
      have := (smul_sub (rotMat α) (x - z) (y - z)).symm
      rw [sub_sub_sub_cancel_right] at this
      calc (rotMat α) • (x - z) + z - ((rotMat α) • (y - z) + z)
          = (rotMat α) • (x - z) - (rotMat α) • (y - z) := by abel
        _ = (rotMat α) • (x - y) := this
    rw [heq]
    exact norm_orthogonal 2 (rotO2 α) (x - y)
  surjective := by
    intro y
    use (rotO2 α)⁻¹ • (y - z) + z
    show (rotMat α) • (((rotO2 α)⁻¹ • (y - z) + z) - z) + z = y
    simp only [add_sub_cancel_right]
    -- rotMat α • v = (rotO2 α) • v for any v
    have key : ∀ v : R2, (rotMat α) • v = (rotO2 α) • v := fun _ => rfl
    rw [key]
    -- Now: (rotO2 α) • ((rotO2 α)⁻¹ • (y - z)) + z = y
    rw [← mul_smul, mul_inv_cancel, one_smul]
    abel

private lemma inner_eq_dotProduct (x y : R2) : @inner ℝ R2 _ x y = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct]; ring

/-
Example 1.2d: reflection in a line through the origin perpendicular to a unit vector w
-/
noncomputable def PlaneIsometry.reflection (w : R2) (hw : w ⬝ᵥ w = 1) : PlaneIsometry where
  toFun x := x - (2 * (w ⬝ᵥ x)) • w
  is_isometry x y := by
    -- Simplify f(x) - f(y) = (x-y) - 2(w⬝(x-y))w using linearity of dot product
    have h1 : (x - (2 * (w ⬝ᵥ x)) • w) - (y - (2 * (w ⬝ᵥ y)) • w)
      = (x - y) - (2 * (w ⬝ᵥ (x - y))) • w := by
      rw [dotProduct_sub]; push_cast; module
    rw [h1]
    set d := x - y
    set c := w ⬝ᵥ d
    -- It suffices to show the squares of the norms are equal
    suffices hsq : ‖d - (2 * c) • w‖ ^ 2 = ‖d‖ ^ 2 by
      nlinarith [norm_nonneg d, norm_nonneg (d - (2 * c) • w),
        sq_nonneg (‖d - (2 * c) • w‖ - ‖d‖)]
    -- Expand ‖d - (2c)w‖² = ‖d‖² - 2·(2c)·⟨d,w⟩ + (2c)²·‖w‖²
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow]
    simp only [Real.norm_eq_abs, sq_abs]
    -- Use ⟨d,w⟩ = w⬝d = c (inner product equals dot product + commutativity)
    have h_inner_dw : @inner ℝ R2 _ d w = c := by
      rw [inner_eq_dotProduct]; exact dotProduct_comm d w
    -- Use ‖w‖² = w⬝w = 1
    have h_norm_w_sq : ‖w‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]; exact hw
    rw [h_inner_dw, h_norm_w_sq]; ring
  surjective := by
    -- The reflection is an involution: f(f(y)) = y, so f(y) is a preimage of y
    intro y
    use y - (2 * (w ⬝ᵥ y)) • w
    -- Compute w⬝f(y) = w⬝(y - 2(w⬝y)w) = w⬝y - 2(w⬝y)(w⬝w) = -(w⬝y)
    have hfy : w ⬝ᵥ (y - (2 * (w ⬝ᵥ y)) • w) = -(w ⬝ᵥ y) := by
      rw [dotProduct_sub, dotProduct_smul, hw, smul_eq_mul]; ring
    show y - (2 * (w ⬝ᵥ y)) • w - (2 * (w ⬝ᵥ (y - (2 * (w ⬝ᵥ y)) • w))) • w = y
    rw [hfy]; push_cast; module
