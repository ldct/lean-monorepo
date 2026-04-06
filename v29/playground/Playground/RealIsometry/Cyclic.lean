import Playground.RealIsometry.Dihedral

set_option linter.style.multiGoal false

/-
Cyclic subgroups of the isometry group
-/

noncomputable section

def rotZ (θ : ℝ) : MAT3 :=
  !![Real.cos θ, -Real.sin θ, 0;
     Real.sin θ, Real.cos θ, 0;
     0, 0, 1]

lemma rotZ_zero : rotZ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ]

lemma rotZ_mul (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  simp only [rotZ, Real.cos_add, Real.sin_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

lemma rotZ_mem_orthogonal (θ : ℝ) : rotZ θ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  constructor <;> {
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring_nf <;>
      simp [Real.sin_sq_add_cos_sq, Real.cos_sq_add_sin_sq]
  }

noncomputable def rotIsometry (θ : ℝ) : SpaceIsometry :=
  multiplication ⟨rotZ θ, rotZ_mem_orthogonal θ⟩

lemma rotIsometry_mul (a b : ℝ) : rotIsometry a * rotIsometry b = rotIsometry (a + b) := by
  ext x : 2
  simp only [mul_eq, RealIsometry.comp, Function.comp, rotIsometry, multiplication]
  rw [← mul_smul]
  congr 1
  exact Subtype.ext (rotZ_mul a b)

private lemma rotIsometry_eq_one_of_rotZ (θ : ℝ) (h : rotZ θ = 1) : rotIsometry θ = 1 := by
  ext x : 2
  simp only [rotIsometry, multiplication, one_eq, RealIsometry.identity]
  change (⟨rotZ θ, _⟩ : O3) • x = id x
  rw [show (⟨rotZ θ, _⟩ : O3) = 1 from Subtype.ext h]
  simp

lemma rotIsometry_zero : rotIsometry 0 = 1 :=
  rotIsometry_eq_one_of_rotZ 0 rotZ_zero

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
      simp_all [rotZ]
    rw [cos_eq_one_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    have hcos : cos (2 * π * ↑k) = 1 := by
      rw [show (2 : ℝ) * π * ↑k = ↑k * (2 * π) from by ring]; simp [cos_int_mul_two_pi]
    have hsin : sin (2 * π * ↑k) = 0 := by
      rw [show (2 : ℝ) * π * ↑k = 0 + ↑k * (2 * π) from by ring, sin_add_int_mul_two_pi, sin_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotZ, hcos, hsin]

lemma rotZ_eq_one_of_rotIsometry_eq_one (θ : ℝ) (h : rotIsometry θ = 1) : rotZ θ = 1 := by
  have h2 := congr_arg RealIsometry.toFun h
  simp only [rotIsometry, multiplication, one_eq, RealIsometry.identity] at h2
  have h3 : ∀ x : R3, (⟨rotZ θ, rotZ_mem_orthogonal θ⟩ : O3) • x = x := congr_fun h2
  have h5 : ∀ x : Fin 3 → ℝ, (rotZ θ).mulVec x = x := fun x =>
    congr_arg (WithLp.equiv 2 _) (h3 ((WithLp.equiv 2 _).symm x))
  exact Matrix.ext_of_mulVec_single fun j => by rw [h5, Matrix.one_mulVec]

lemma rotIsometry_eq_one_iff (θ : ℝ) : rotIsometry θ = 1 ↔ ∃ k : ℤ, θ = 2 * Real.pi * k := by
  constructor
  · exact fun h => (rotZ_eq_one_iff θ).mp (rotZ_eq_one_of_rotIsometry_eq_one θ h)
  · exact fun ⟨k, hk⟩ => rotIsometry_eq_one_of_rotZ θ ((rotZ_eq_one_iff θ).mpr ⟨k, hk⟩)

open Real in
lemma rotIsometry_pow_eq_one_iff (θ : ℝ) (m : ℕ) :
    rotIsometry θ ^ m = 1 ↔ ∃ k : ℤ, (m : ℝ) * θ = 2 * π * (k : ℝ) := by
  rw [rotIsometry_pow, rotIsometry_eq_one_iff]

open Real in
lemma orderOf_rotIsometry (n : ℕ) (hn : n ≠ 0) :
    orderOf (rotIsometry (2 * π / n)) = n := by
  sorry

open Real in
lemma rotIsometry_generates_cyclic (n : ℕ) (_hn : n ≠ 0) :
    Subgroup.zpowers (rotIsometry (2 * π / n)) = Subgroup.closure {rotIsometry (2 * π / n)} := by
  rw [Subgroup.zpowers_eq_closure]

end
