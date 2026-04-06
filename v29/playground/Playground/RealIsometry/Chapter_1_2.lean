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
    ext i j; fin_cases i <;> fin_cases j
    <;> simp [rotMat, Matrix.mul_apply]
    <;> grind [Real.sin_sq_add_cos_sq, Real.cos_sq_add_sin_sq]
  constructor
  · exact hRT
  · grind [
    Matrix.mul_eq_one_comm,
    Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial
  ]

private noncomputable def rotO2 (α : ℝ) : O2 := ⟨rotMat α, rotMat_orthogonal α⟩

noncomputable def PlaneIsometry.r0 (α : ℝ) : PlaneIsometry where
  toFun x := !![Real.cos α, -Real.sin α; Real.sin α, Real.cos α]  • x
  is_isometry x y := calc
      _ = ‖(rotMat α) • x - (rotMat α) • y‖ := by rfl
      _ = ‖rotMat α • (x - y)‖ := by rw [← smul_sub]
      _ = ‖x - y‖ := norm_orthogonal _ (rotO2 α) _
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
  simp [PiLp.inner_apply, inner, dotProduct]; ring

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
      exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq
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

/-
Example 1.2e: glide reflection in a line through the origin perpendicular to a unit vector w,
with translation d along the line (w ⬝ᵥ d = 0)
-/
noncomputable def PlaneIsometry.glideReflection0 (w : R2) (hw : w ⬝ᵥ w = 1)
    (d : R2) (hd : w ⬝ᵥ d = 0) : PlaneIsometry where
  toFun x := x - (2 * (w ⬝ᵥ x)) • w + d
  is_isometry x y := by
    -- The +d terms cancel: f(x) - f(y) = (x-y) - 2(w⬝(x-y))w
    have h1 : (x - (2 * (w ⬝ᵥ x)) • w + d) - (y - (2 * (w ⬝ᵥ y)) • w + d)
      = (x - y) - (2 * (w ⬝ᵥ (x - y))) • w := by
      rw [dotProduct_sub]; push_cast; module
    rw [h1]
    set u := x - y
    set c := w ⬝ᵥ u
    suffices hsq : ‖u - (2 * c) • w‖ ^ 2 = ‖u‖ ^ 2 by
      exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow]
    simp only [Real.norm_eq_abs, sq_abs]
    have h_inner : @inner ℝ R2 _ u w = c := by
      rw [inner_eq_dotProduct]; exact dotProduct_comm u w
    have h_norm_w : ‖w‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]; exact hw
    rw [h_inner, h_norm_w]; ring
  surjective := by
    intro y
    use y - d - (2 * (w ⬝ᵥ (y - d))) • w
    -- Key: reflection is involution, so w⬝f⁻¹(y) = -(w⬝(y-d))
    have hinv : w ⬝ᵥ (y - d - (2 * (w ⬝ᵥ (y - d))) • w) = -(w ⬝ᵥ (y - d)) := by
      rw [dotProduct_sub, dotProduct_smul, hw, smul_eq_mul]; ring
    show y - d - (2 * (w ⬝ᵥ (y - d))) • w -
      (2 * (w ⬝ᵥ (y - d - (2 * (w ⬝ᵥ (y - d))) • w))) • w + d = y
    rw [hinv]; push_cast; module

/-
Example 1.2f: general glide reflection in a line through p perpendicular to a unit vector w,
with translation d along the line (w ⬝ᵥ d = 0)
-/
noncomputable def PlaneIsometry.glideReflection (w : R2) (hw : w ⬝ᵥ w = 1)
    (p d : R2) (hd : w ⬝ᵥ d = 0) : PlaneIsometry where
  toFun x := x - (2 * (w ⬝ᵥ (x - p))) • w + d
  is_isometry x y := by
    -- The +d and p terms cancel: f(x) - f(y) = (x-y) - 2(w⬝(x-y))w
    have h1 : (x - (2 * (w ⬝ᵥ (x - p))) • w + d) - (y - (2 * (w ⬝ᵥ (y - p))) • w + d)
      = (x - y) - (2 * (w ⬝ᵥ (x - y))) • w := by
      have hdot : w ⬝ᵥ (x - y) = w ⬝ᵥ (x - p) - w ⬝ᵥ (y - p) := by
        rw [dotProduct_sub, dotProduct_sub, dotProduct_sub]; ring
      rw [hdot]; module
    rw [h1]
    set u := x - y
    set c := w ⬝ᵥ u
    suffices hsq : ‖u - (2 * c) • w‖ ^ 2 = ‖u‖ ^ 2 by
      exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow]
    simp only [Real.norm_eq_abs, sq_abs]
    have h_inner : @inner ℝ R2 _ u w = c := by
      rw [inner_eq_dotProduct]; exact dotProduct_comm u w
    have h_norm_w : ‖w‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]; exact hw
    rw [h_inner, h_norm_w]; ring
  surjective := by
    intro y
    use y - (2 * (w ⬝ᵥ (y - p))) • w - d
    -- Key: w⬝((y - 2c·w - d) - p) = -(w⬝(y-p))
    have hinv : w ⬝ᵥ ((y - (2 * (w ⬝ᵥ (y - p))) • w - d) - p) = -(w ⬝ᵥ (y - p)) := by
      rw [dotProduct_sub, dotProduct_sub, dotProduct_sub, dotProduct_smul, smul_eq_mul,
        hw, hd, dotProduct_sub]; ring
    show (y - (2 * (w ⬝ᵥ (y - p))) • w - d) -
      (2 * (w ⬝ᵥ ((y - (2 * (w ⬝ᵥ (y - p))) • w - d) - p))) • w + d = y
    rw [hinv]; push_cast; module
