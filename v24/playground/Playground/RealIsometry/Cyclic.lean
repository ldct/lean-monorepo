import Playground.RealIsometry.Basic

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Real in
noncomputable def rotZ (θ : ℝ) : MAT3 := ![
  ![cos θ, -sin θ, 0],
  ![sin θ,  cos θ, 0],
  ![0,     0,      1]]

open Real in
lemma rotZ_transpose (θ : ℝ) : (rotZ θ).transpose = rotZ (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.transpose_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
          Real.cos_neg, Real.sin_neg]

open Real in
lemma rotZ_mul (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.head_fin_const, Real.cos_add, Real.sin_add]
  all_goals ring

open Real in
lemma rotZ_zero : rotZ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.one_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]

lemma star_rotZ (θ : ℝ) : star (rotZ θ) = rotZ (-θ) := by
  -- star for matrices is conjTranspose, which equals transpose for real matrices
  change (rotZ θ).conjTranspose = rotZ (-θ)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, rotZ_transpose]

lemma rotZ_mem_orthogonal (θ : ℝ) : rotZ θ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  change rotZ θ * star (rotZ θ) = 1
  rw [star_rotZ, rotZ_mul, add_neg_cancel, rotZ_zero]

noncomputable def rotIsometry (θ : ℝ) : SpaceIsometry :=
  multiplication ⟨rotZ θ, rotZ_mem_orthogonal θ⟩

lemma rotIsometry_mul (a b : ℝ) : rotIsometry a * rotIsometry b = rotIsometry (a + b) := by
  ext x : 2
  simp only [mul_eq, RealIsometry.comp, Function.comp, rotIsometry, multiplication]
  rw [← mul_smul]
  congr 1
  exact Subtype.ext (rotZ_mul a b)

lemma rotIsometry_zero : rotIsometry 0 = 1 := by
  ext x : 2
  simp only [rotIsometry, multiplication, one_eq, RealIsometry.identity]
  change (rotZ 0).mulVec x = x
  rw [rotZ_zero]
  exact Matrix.one_mulVec x

lemma rotIsometry_pow (θ : ℝ) (n : ℕ) : rotIsometry θ ^ n = rotIsometry (n * θ) := by
  induction n with
  | zero => simp [rotIsometry_zero]
  | succ n ih =>
    rw [pow_succ, ih, rotIsometry_mul]
    congr 1; push_cast; ring

-- rotIsometry_zpow is not needed for the main theorem

open Real in
lemma rotZ_eq_one_iff (θ : ℝ) : rotZ θ = 1 ↔ ∃ k : ℤ, θ = 2 * π * k := by
  constructor
  · intro h
    have hcos : cos θ = 1 := by
      have := congr_fun (congr_fun h 0) 0
      simp [rotZ, Matrix.one_apply, Matrix.cons_val_zero, Matrix.head_cons] at this
      exact this
    rw [cos_eq_one_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    exact ⟨k, by linarith⟩
  · intro ⟨k, hk⟩
    subst hk
    have hcos : cos (2 * π * ↑k) = 1 := by
      rw [show (2 : ℝ) * π * ↑k = ↑k * (2 * π) from by ring]
      exact cos_int_mul_two_pi k
    have hsin : sin (2 * π * ↑k) = 0 := by
      rw [show (2 : ℝ) * π * ↑k = 0 + ↑k * (2 * π) from by ring]
      rw [sin_add_int_mul_two_pi, sin_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.one_apply, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, hcos, hsin]

lemma rotZ_eq_one_of_rotIsometry_eq_one (θ : ℝ) (h : rotIsometry θ = 1) : rotZ θ = 1 := by
  have h2 := congr_arg RealIsometry.toFun h
  simp only [rotIsometry, multiplication, one_eq, RealIsometry.identity] at h2
  have h4 : ∀ x : R3, (rotZ θ).mulVec x = x := congr_fun h2
  exact Matrix.ext_of_mulVec_single fun j => by rw [h4, Matrix.one_mulVec]

lemma rotIsometry_eq_one_iff (θ : ℝ) : rotIsometry θ = 1 ↔ ∃ k : ℤ, θ = 2 * Real.pi * k := by
  constructor
  · intro h
    exact (rotZ_eq_one_iff θ).mp (rotZ_eq_one_of_rotIsometry_eq_one θ h)
  · intro ⟨k, hk⟩
    have : rotZ θ = 1 := (rotZ_eq_one_iff θ).mpr ⟨k, hk⟩
    ext x : 2
    simp only [rotIsometry, multiplication, one_eq, RealIsometry.identity]
    change (rotZ θ).mulVec x = x
    rw [this]; exact Matrix.one_mulVec x

open Real in
lemma rotIsometry_pow_eq_one_iff (θ : ℝ) (m : ℕ) :
    rotIsometry θ ^ m = 1 ↔ ∃ k : ℤ, (m : ℝ) * θ = 2 * π * (k : ℝ) := by
  rw [rotIsometry_pow, rotIsometry_eq_one_iff]

open Real in
lemma orderOf_rotIsometry (n : ℕ) (hn : n ≠ 0) :
    orderOf (rotIsometry (2 * π / n)) = n := by
  rw [orderOf_eq_iff (Nat.pos_of_ne_zero hn)]
  refine ⟨?_, ?_⟩
  · -- rotIsometry(2π/n) ^ n = 1
    rw [rotIsometry_pow_eq_one_iff]
    refine ⟨1, ?_⟩; push_cast; field_simp
  · -- For 0 < m < n, rotIsometry(2π/n) ^ m ≠ 1
    intro m hm hm0
    simp only [ne_eq, rotIsometry_pow_eq_one_iff]
    push_neg
    intro k heq
    have hpi : (0 : ℝ) < π := pi_pos
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have h1 : (m : ℝ) = (n : ℝ) * (k : ℝ) := by
      have : (m : ℝ) * (2 * π / ↑n) = 2 * π * ↑k := heq
      field_simp at this
      linarith
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    have hk_pos : (0 : ℝ) < k := by
      by_contra hk_le
      push_neg at hk_le
      -- hk_le : ↑k ≤ 0 in ℝ
      linarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hn') hk_le]
    have hm_lt : (m : ℝ) < n := Nat.cast_lt.mpr hm
    -- From h1: m = n*k, and 0 < m < n, 0 < k (as reals)
    -- So n*k < n, hence k < 1
    -- From h1 and hm_lt: n*k < n, so k < 1 (in ℝ)
    -- But k is a positive integer, so k ≥ 1, contradiction
    have hk_int_pos : 1 ≤ k := Int.lt_iff_add_one_le.mp (by exact_mod_cast hk_pos)
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_int_pos
    have : (n : ℝ) * (k : ℝ) < n := h1 ▸ hm_lt
    nlinarith

def IsCyclicOfOrder (n : ℕ) (G : Type*) [Group G] : Prop :=
  IsCyclic G ∧ Nat.card G = n

open Real in
theorem RealIsometry.isCyclicOfOrder (n : ℕ) [NeZero n]
: ∃ f : Subgroup SpaceIsometry, IsCyclicOfOrder n f := by
  set g := rotIsometry (2 * π / n)
  refine ⟨Subgroup.zpowers g, ?_, ?_⟩
  · -- IsCyclic (zpowers g)
    exact (Subgroup.zpowers g).isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, rfl⟩
  · -- Nat.card (zpowers g) = n
    rw [Nat.card_zpowers]
    exact orderOf_rotIsometry n (NeZero.ne n)
