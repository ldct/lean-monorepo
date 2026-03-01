import Playground.RealIsometry

set_option linter.style.longLine false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000

open Real Matrix

/-! ## Rotation and reflection matrices in ℝ³ -/

noncomputable def rotMat (θ : ℝ) : MAT :=
  !![cos θ, -(sin θ), 0; sin θ, cos θ, 0; 0, 0, 1]

def reflMat : MAT :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 1]

noncomputable def dihedralAngle (n : ℕ) : ℝ := 2 * π / n

noncomputable def rotMatZMod (n : ℕ) [NeZero n] (k : ZMod n) : MAT :=
  rotMat (ZMod.val k * dihedralAngle n)

/-! ## Basic matrix identities -/

lemma rotMat_mul (θ₁ θ₂ : ℝ) : rotMat θ₁ * rotMat θ₂ = rotMat (θ₁ + θ₂) := by
  ext i j
  simp only [rotMat, mul_apply, Fin.sum_univ_three,
    of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const, cos_add, sin_add]
  fin_cases i <;> fin_cases j <;> simp <;> ring

lemma rotMat_zero : rotMat 0 = 1 := by
  ext i j
  simp only [rotMat, cos_zero, sin_zero, neg_zero,
    of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const]
  fin_cases i <;> fin_cases j <;> simp [one_apply]

lemma rotMat_periodic (θ : ℝ) (k : ℤ) : rotMat (θ + k * (2 * π)) = rotMat θ := by
  simp [rotMat, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

lemma reflMat_mul_self : reflMat * reflMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflMat, mul_apply, one_apply, of_apply, cons_val', cons_val_zero,
      cons_val_one, head_cons, head_fin_const, Fin.sum_univ_three]

lemma rotMat_reflMat_eq (θ : ℝ) : rotMat θ * reflMat = reflMat * rotMat (-θ) := by
  ext i j
  simp only [rotMat, reflMat, mul_apply, Fin.sum_univ_three,
    of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const, cos_neg, sin_neg]
  fin_cases i <;> fin_cases j <;> simp

/-! ## Orthogonality -/

lemma rotMat_mem_O3 (θ : ℝ) : rotMat θ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [mem_orthogonalGroup_iff']
  ext i j
  simp only [rotMat, transpose_apply, mul_apply, Fin.sum_univ_three,
    of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const]
  fin_cases i <;> fin_cases j <;> simp [one_apply] <;> nlinarith [sin_sq_add_cos_sq θ]

lemma reflMat_mem_O3 : reflMat ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [mem_orthogonalGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflMat, transpose_apply, mul_apply, one_apply,
      of_apply, cons_val', cons_val_zero, cons_val_one,
      head_cons, head_fin_const, Fin.sum_univ_three]

lemma mul_mem_O3 {A B : MAT}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hB : B ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    : A * B ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [mem_orthogonalGroup_iff'] at *
  calc (A * B).transpose * (A * B)
      = B.transpose * A.transpose * (A * B) := by rw [transpose_mul]
    _ = B.transpose * (A.transpose * A) * B := by simp [Matrix.mul_assoc]
    _ = B.transpose * 1 * B := by rw [hA]
    _ = B.transpose * B := by rw [Matrix.mul_one]
    _ = 1 := hB

/-! ## Angle arithmetic -/

lemma n_mul_angle (n : ℕ) [NeZero n] : (↑n : ℝ) * dihedralAngle n = 2 * π := by
  simp only [dihedralAngle]; rw [mul_comm, div_mul_cancel₀]
  exact Nat.cast_ne_zero.mpr (NeZero.ne n)

lemma rotMatZMod_eq_rotMat (n : ℕ) [NeZero n] (k : ℤ) (a : ZMod n) (h : (k : ZMod n) = a) :
    rotMatZMod n a = rotMat (↑k * dihedralAngle n) := by
  simp only [rotMatZMod]
  obtain ⟨q, hq⟩ : (↑n : ℤ) ∣ (↑(ZMod.val a) - k) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [ZMod.natCast_val]; simp [ZMod.intCast_cast, h]
  have hval : (↑(ZMod.val a) : ℝ) = ↑k + ↑n * ↑q := by
    exact_mod_cast (show (↑(ZMod.val a) : ℤ) = k + ↑n * q from by omega)
  rw [hval, add_mul, mul_assoc,
    show (↑n : ℝ) * (↑q * dihedralAngle n) = ↑q * (↑n * dihedralAngle n) from by ring,
    n_mul_angle, rotMat_periodic]

lemma rotMat_eq_rotMatZMod (n : ℕ) [NeZero n] (k : ℤ) :
    rotMat (↑k * dihedralAngle n) = rotMatZMod n (k : ZMod n) := by
  exact (rotMatZMod_eq_rotMat n k _ rfl).symm

/-! ## rotMatZMod properties -/

lemma rotMatZMod_add (n : ℕ) [NeZero n] (i j : ZMod n) :
    rotMatZMod n i * rotMatZMod n j = rotMatZMod n (i + j) := by
  simp only [rotMatZMod, rotMat_mul, ← add_mul]
  -- Goal: rotMat((val i + val j) * angle) = rotMat(val(i+j) * angle)
  -- Both equal rotMatZMod n (i+j) via rotMatZMod_eq_rotMat
  rw [show rotMat (↑(ZMod.val (i + j)) * dihedralAngle n) = rotMatZMod n (i + j) from rfl]
  rw [rotMatZMod_eq_rotMat n (↑(ZMod.val i) + ↑(ZMod.val j)) (i + j)
    (by push_cast [ZMod.natCast_val]; simp)]
  congr 1; push_cast; ring

lemma rotMatZMod_zero (n : ℕ) [NeZero n] : rotMatZMod n 0 = 1 := by
  simp [rotMatZMod, ZMod.val_zero, rotMat_zero]

/-! ## reflMat * rotMat(θ) ≠ rotMat(φ) -/

lemma reflMat_mul_rotMat_ne_rotMat (θ φ : ℝ) : reflMat * rotMat θ ≠ rotMat φ := by
  intro h
  have h00 : cos θ = cos φ := by
    have := congr_fun₂ h 0 0
    simp [rotMat, reflMat, mul_apply, Fin.sum_univ_three, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const] at this; linarith
  have h11 : -cos θ = cos φ := by
    have := congr_fun₂ h 1 1
    simp [rotMat, reflMat, mul_apply, Fin.sum_univ_three, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const] at this; linarith
  have hcos : cos θ = 0 := by linarith
  have hsin : sin θ = 0 := by
    have h10 : -sin θ = sin φ := by
      have := congr_fun₂ h 1 0
      simp [rotMat, reflMat, mul_apply, Fin.sum_univ_three, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const] at this; linarith
    have h01 : sin θ = sin φ := by
      have := congr_fun₂ h 0 1
      simp [rotMat, reflMat, mul_apply, Fin.sum_univ_three, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const] at this; linarith
    linarith
  nlinarith [sin_sq_add_cos_sq θ]

/-! ## rotMat equality and rotMatZMod injectivity -/

lemma rotMat_eq_iff (θ₁ θ₂ : ℝ) : rotMat θ₁ = rotMat θ₂ ↔ ∃ k : ℤ, θ₁ - θ₂ = k * (2 * π) := by
  constructor
  · intro h
    have hcos : cos θ₁ = cos θ₂ := by
      have := congr_fun₂ h 0 0
      simp [rotMat, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const] at this; linarith
    have hsin : sin θ₁ = sin θ₂ := by
      have := congr_fun₂ h 1 0
      simp [rotMat, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, head_fin_const] at this; linarith
    have hcos_diff : cos (θ₁ - θ₂) = 1 := by
      rw [cos_sub, hcos, hsin]; nlinarith [sin_sq_add_cos_sq θ₂]
    rw [cos_eq_one_iff] at hcos_diff
    obtain ⟨k, hk⟩ := hcos_diff; exact ⟨k, hk.symm⟩
  · intro ⟨k, hk⟩
    have : θ₁ = θ₂ + k * (2 * π) := by linarith
    subst this; exact rotMat_periodic _ _

lemma rotMatZMod_injective (n : ℕ) [NeZero n] : Function.Injective (rotMatZMod n) := by
  intro i j h
  simp only [rotMatZMod] at h; rw [rotMat_eq_iff] at h; obtain ⟨k, hk⟩ := h
  have hvi := ZMod.val_lt i; have hvj := ZMod.val_lt j
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hk_eq : (↑(ZMod.val i) : ℝ) - ↑(ZMod.val j) = ↑k * ↑n := by
    simp only [dihedralAngle] at hk; field_simp at hk; linarith
  suffices hk0 : k = 0 by
    rw [hk0, Int.cast_zero, zero_mul] at hk_eq
    exact (ZMod.val_injective n) (Nat.cast_injective (show (ZMod.val i : ℝ) = ZMod.val j by linarith))
  by_contra hk_ne
  have h1 : (1 : ℝ) ≤ |(↑k : ℝ)| := by exact_mod_cast Int.one_le_abs hk_ne
  have h2 : |(↑(ZMod.val i) : ℝ) - ↑(ZMod.val j)| < ↑n := by
    rw [abs_lt]; constructor
    · linarith [Nat.cast_nonneg (α := ℝ) (ZMod.val i), Nat.cast_lt (α := ℝ).mpr hvj]
    · linarith [Nat.cast_nonneg (α := ℝ) (ZMod.val j), Nat.cast_lt (α := ℝ).mpr hvi]
  rw [hk_eq, abs_mul, show |(↑n : ℝ)| = ↑n from abs_of_pos hn_pos] at h2
  linarith [le_mul_of_one_le_left (le_of_lt hn_pos) h1]

/-! ## The dihedral homomorphism -/

noncomputable def dihedralToMat (n : ℕ) [NeZero n] : DihedralGroup n → MAT
  | .r k => rotMatZMod n k
  | .sr k => reflMat * rotMatZMod n k

lemma dihedralToMat_mem_O3 (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    dihedralToMat n g ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  cases g with
  | r k => exact rotMat_mem_O3 _
  | sr k => exact mul_mem_O3 reflMat_mem_O3 (rotMat_mem_O3 _)

lemma dihedralToMat_one (n : ℕ) [NeZero n] : dihedralToMat n 1 = 1 := by
  show dihedralToMat n (DihedralGroup.r 0) = 1; simp [dihedralToMat, rotMatZMod_zero]

lemma dihedralToMat_mul (n : ℕ) [NeZero n] (a b : DihedralGroup n) :
    dihedralToMat n (a * b) = dihedralToMat n a * dihedralToMat n b := by
  cases a with
  | r i => cases b with
    | r j =>
      simp only [DihedralGroup.r_mul_r, dihedralToMat]
      exact (rotMatZMod_add n i j).symm
    | sr j =>
      -- r i * sr j = sr (j - i)
      -- Need: reflMat * R(j-i) = R(i) * (reflMat * R(j))
      simp only [DihedralGroup.r_mul_sr, dihedralToMat, rotMatZMod]
      rw [← Matrix.mul_assoc, rotMat_reflMat_eq, Matrix.mul_assoc, rotMat_mul]
      -- Goal: reflMat * rotMat(val(j-i)*θ) = reflMat * rotMat(-val(i)*θ + val(j)*θ)
      congr 1
      calc rotMat (↑(ZMod.val (j - i)) * dihedralAngle n)
          = rotMatZMod n (j - i) := rfl
        _ = rotMat ((-↑(ZMod.val i) + ↑(ZMod.val j)) * dihedralAngle n) := by
            rw [rotMatZMod_eq_rotMat n (-↑(ZMod.val i) + ↑(ZMod.val j)) (j - i)
              (by push_cast [ZMod.natCast_val]; ring)]
            congr 1; push_cast; ring
        _ = rotMat (-((↑(ZMod.val i) : ℝ) * dihedralAngle n) + ↑(ZMod.val j) * dihedralAngle n) := by
            congr 1; ring
  | sr i => cases b with
    | r j =>
      -- sr i * r j = sr (i + j)
      simp only [DihedralGroup.sr_mul_r, dihedralToMat]
      rw [Matrix.mul_assoc, rotMatZMod_add]
    | sr j =>
      -- sr i * sr j = r (j - i)
      -- (refl * R(i)) * (refl * R(j)) = refl * R(i) * refl * R(j)
      --   = refl * (R(i) * refl) * R(j) = refl * refl * R(-i) * R(j)
      --   = R(-i) * R(j) = R(j-i)
      simp only [DihedralGroup.sr_mul_sr, dihedralToMat, rotMatZMod]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rotMat _) reflMat,
          rotMat_reflMat_eq, ← Matrix.mul_assoc reflMat, ← Matrix.mul_assoc reflMat,
          reflMat_mul_self, Matrix.one_mul, rotMat_mul]
      -- Goal: rotMat(val(j-i)*θ) = rotMat(-val(i)*θ + val(j)*θ)
      calc rotMat (↑(ZMod.val (j - i)) * dihedralAngle n)
          = rotMatZMod n (j - i) := rfl
        _ = rotMat ((-↑(ZMod.val i) + ↑(ZMod.val j)) * dihedralAngle n) := by
            rw [rotMatZMod_eq_rotMat n (-↑(ZMod.val i) + ↑(ZMod.val j)) (j - i)
              (by push_cast [ZMod.natCast_val]; ring)]
            congr 1; push_cast; ring
        _ = rotMat (-((↑(ZMod.val i) : ℝ) * dihedralAngle n) + ↑(ZMod.val j) * dihedralAngle n) := by
            congr 1; ring

lemma dihedralToMat_injective (n : ℕ) [NeZero n] : Function.Injective (dihedralToMat n) := by
  intro a b hab
  cases a with
  | r i => cases b with
    | r j => exact congrArg _ (rotMatZMod_injective n (by simpa [dihedralToMat] using hab))
    | sr j =>
      have := (by simpa [dihedralToMat] using hab : rotMatZMod n i = reflMat * rotMatZMod n j).symm
      exact absurd this (reflMat_mul_rotMat_ne_rotMat _ _)
  | sr i => cases b with
    | r j => exact absurd (by simpa [dihedralToMat] using hab) (reflMat_mul_rotMat_ne_rotMat _ _)
    | sr j =>
      simp only [dihedralToMat] at hab
      have hcancel : rotMatZMod n i = rotMatZMod n j := by
        have h1 : reflMat * (reflMat * rotMatZMod n i) = reflMat * (reflMat * rotMatZMod n j) :=
          congr_arg (reflMat * ·) hab
        rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, reflMat_mul_self, Matrix.one_mul, Matrix.one_mul] at h1
      exact congrArg _ (rotMatZMod_injective n hcancel)

/-! ## Lifting to RealIsometry -/

noncomputable def multiplicationHom : O3 →* RealIsometry where
  toFun A := multiplication A
  map_one' := by ext x : 2; simp [multiplication]; rfl
  map_mul' A B := by
    ext x : 2
    simp only [multiplication, mul_eq, RealIsometry.comp, Function.comp]
    show (A * B).1 • x = A.1 • (B.1 • x)
    rw [← MulAction.mul_smul]; rfl

lemma multiplicationHom_injective : Function.Injective multiplicationHom := by
  intro A B h
  have key : ∀ x : R3, (A : MAT).mulVec x = (B : MAT).mulVec x := by
    intro x
    have := congr_fun (congr_arg RealIsometry.toFun h) x
    change (multiplication A).toFun x = (multiplication B).toFun x at this
    simp only [multiplication] at this; exact this
  exact Subtype.ext (Matrix.ext_of_mulVec_single fun j => key _)

noncomputable def dihedralToIsometry (n : ℕ) [NeZero n] : DihedralGroup n →* RealIsometry where
  toFun g := multiplicationHom ⟨dihedralToMat n g, dihedralToMat_mem_O3 n g⟩
  map_one' := by
    change multiplicationHom ⟨dihedralToMat n 1, _⟩ = 1
    have : dihedralToMat n 1 = 1 := dihedralToMat_one n
    simp only [this]; exact multiplicationHom.map_one
  map_mul' a b := by
    change multiplicationHom ⟨_, _⟩ = multiplicationHom ⟨_, _⟩ * multiplicationHom ⟨_, _⟩
    rw [← multiplicationHom.map_mul]
    have : dihedralToMat n (a * b) = dihedralToMat n a * dihedralToMat n b := dihedralToMat_mul n a b
    congr 1; exact Subtype.ext this

lemma dihedralToIsometry_injective (n : ℕ) [NeZero n] :
    Function.Injective (dihedralToIsometry n) := by
  intro a b hab
  apply dihedralToMat_injective n
  have h : multiplicationHom ⟨dihedralToMat n a, dihedralToMat_mem_O3 n a⟩ =
           multiplicationHom ⟨dihedralToMat n b, dihedralToMat_mem_O3 n b⟩ := hab
  have := multiplicationHom_injective h
  exact congrArg Subtype.val this

/-! ## Main theorem -/

theorem RealIsometry.hasDihedralSubgroup (n : ℕ) [NeZero n]
    : ∃ f : Subgroup RealIsometry, Nonempty (DihedralGroup n ≃* f) :=
  ⟨(dihedralToIsometry n).range, ⟨MonoidHom.ofInjective (dihedralToIsometry_injective n)⟩⟩
