import Playground.RealIsometry.Basic
import Playground.RealIsometry.Dihedral

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.nativeDecide false
set_option linter.style.show false

open Matrix

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

def IsExceptional (H : Subgroup SpaceIsometry) : Prop :=
  ¬ IsCyclic H ∧ ¬ IsDihedral H ∧ Nat.card H ≠ 0

/-! ## Tetrahedral rotation group (A₄) as a subgroup of RealIsometry

We realize A₄ as the rotation group of a regular tetrahedron inscribed in a cube
with vertices at (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1).

The 12 rotations are:
- 1 identity (order 1)
- 3 rotations by 180° about coordinate axes (order 2)
- 8 rotations by ±120° about body diagonals (order 3)

Element orders: 1 appears 1×, 2 appears 3×, 3 appears 8×.
Every element satisfies g² = 1 or g³ = 1, so the exponent divides 6.
-/

/-! ### Integer matrices and casting infrastructure -/

abbrev IMAT := Matrix (Fin 3) (Fin 3) ℤ

#check Matrix.zpow_add
#check Matrix.map_mul

#synth HPow IMAT ℕ IMAT

abbrev Matrix.toReal (M : IMAT) : MAT := M.map (Int.castRingHom ℝ)

lemma toReal_mul (A B : IMAT) : (A * B).toReal = A.toReal * B.toReal := by
  grind [Matrix.map_mul]

lemma toReal_one : toReal 1 = (1 : MAT) := by simp

lemma toReal_pow (A : IMAT) (n : ℕ) : toReal (A ^ n) = (toReal A) ^ n := by
  induction n with
  | zero => simp [pow_zero, toReal_one]
  | succ n ih => rw [pow_succ, toReal_mul, ih, pow_succ]

#check Matrix.map_mul

example
  (α : Type*)
  [Ring α]
  (A : Matrix (Fin 3) (Fin 3) α)
  (B : Matrix (Fin 3) (Fin 3) α)
  (f : α →+* α)
: (A * B).map f = (A.map f) * (B.map f) := Matrix.map_mul

example
  (α : Type*) (k : Nat)
  [Ring α]
  (A : Matrix (Fin 3) (Fin 3) α)
  (B : Matrix (Fin 3) (Fin 3) α)
  (f : α →+* α)
: (A.map f)^k = (A^k).map f := by sorry

lemma toReal_injective : Function.Injective toReal := by
  apply Matrix.map_injective
  exact RingHom.injective_int _

lemma toReal_transpose (A : IMAT) : toReal A.transpose = (toReal A).transpose := by
  ext i j; simp [toReal, map_apply, transpose_apply]

/-! ### The 12 integer matrices of the tetrahedral rotation group -/

def a4MatZ : Fin 12 → IMAT
  | 0  => !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  | 1  => !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  | 2  => !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  | 3  => !![1, 0, 0; 0, -1, 0; 0, 0, -1]
  | 4  => !![0, 1, 0; 0, 0, -1; -1, 0, 0]
  | 5  => !![0, 0, 1; -1, 0, 0; 0, -1, 0]
  | 6  => !![0, 0, -1; 1, 0, 0; 0, -1, 0]
  | 7  => !![0, -1, 0; 0, 0, 1; -1, 0, 0]
  | 8  => !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
  | 9  => !![0, -1, 0; 0, 0, -1; 1, 0, 0]
  | 10 => !![0, 0, -1; -1, 0, 0; 0, 1, 0]
  | 11 => !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The real matrix corresponding to the k-th A₄ element -/
def a4Mat (k : Fin 12) : MAT := toReal (a4MatZ k)

/-! ### Multiplication table (fully explicit for decide) -/

def a4MulTable : Fin 12 → Fin 12 → Fin 12 := fun i j =>
  match i, j with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2 | 0, 3 => 3 | 0, 4 => 4 | 0, 5 => 5 | 0, 6 => 6 | 0, 7 => 7 | 0, 8 => 8 | 0, 9 => 9 | 0, 10 => 10 | 0, 11 => 11
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 0 | 1, 3 => 6 | 1, 4 => 8 | 1, 5 => 7 | 1, 6 => 9 | 1, 7 => 11 | 1, 8 => 10 | 1, 9 => 3 | 1, 10 => 4 | 1, 11 => 5
  | 2, 0 => 2 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => 9 | 2, 4 => 10 | 2, 5 => 11 | 2, 6 => 3 | 2, 7 => 5 | 2, 8 => 4 | 2, 9 => 6 | 2, 10 => 8 | 2, 11 => 7
  | 3, 0 => 3 | 3, 1 => 5 | 3, 2 => 4 | 3, 3 => 0 | 3, 4 => 2 | 3, 5 => 1 | 3, 6 => 10 | 3, 7 => 9 | 3, 8 => 11 | 3, 9 => 7 | 3, 10 => 6 | 3, 11 => 8
  | 4, 0 => 4 | 4, 1 => 3 | 4, 2 => 5 | 4, 3 => 7 | 4, 4 => 6 | 4, 5 => 8 | 4, 6 => 0 | 4, 7 => 1 | 4, 8 => 2 | 4, 9 => 10 | 4, 10 => 11 | 4, 11 => 9
  | 5, 0 => 5 | 5, 1 => 4 | 5, 2 => 3 | 5, 3 => 10 | 5, 4 => 11 | 5, 5 => 9 | 5, 6 => 7 | 5, 7 => 8 | 5, 8 => 6 | 5, 9 => 0 | 5, 10 => 2 | 5, 11 => 1
  | 6, 0 => 6 | 6, 1 => 7 | 6, 2 => 8 | 6, 3 => 1 | 6, 4 => 0 | 6, 5 => 2 | 6, 6 => 4 | 6, 7 => 3 | 6, 8 => 5 | 6, 9 => 11 | 6, 10 => 9 | 6, 11 => 10
  | 7, 0 => 7 | 7, 1 => 8 | 7, 2 => 6 | 7, 3 => 4 | 7, 4 => 5 | 7, 5 => 3 | 7, 6 => 11 | 7, 7 => 10 | 7, 8 => 9 | 7, 9 => 1 | 7, 10 => 0 | 7, 11 => 2
  | 8, 0 => 8 | 8, 1 => 6 | 8, 2 => 7 | 8, 3 => 11 | 8, 4 => 9 | 8, 5 => 10 | 8, 6 => 1 | 8, 7 => 2 | 8, 8 => 0 | 8, 9 => 4 | 8, 10 => 5 | 8, 11 => 3
  | 9, 0 => 9 | 9, 1 => 11 | 9, 2 => 10 | 9, 3 => 2 | 9, 4 => 1 | 9, 5 => 0 | 9, 6 => 8 | 9, 7 => 6 | 9, 8 => 7 | 9, 9 => 5 | 9, 10 => 3 | 9, 11 => 4
  | 10, 0 => 10 | 10, 1 => 9 | 10, 2 => 11 | 10, 3 => 5 | 10, 4 => 3 | 10, 5 => 4 | 10, 6 => 2 | 10, 7 => 0 | 10, 8 => 1 | 10, 9 => 8 | 10, 10 => 7 | 10, 11 => 6
  | 11, 0 => 11 | 11, 1 => 10 | 11, 2 => 9 | 11, 3 => 8 | 11, 4 => 7 | 11, 5 => 6 | 11, 6 => 5 | 11, 7 => 4 | 11, 8 => 3 | 11, 9 => 2 | 11, 10 => 1 | 11, 11 => 0

def a4InvTable : Fin 12 → Fin 12 := fun i =>
  match i with
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 9
  | 6 => 4 | 7 => 10 | 8 => 8 | 9 => 5 | 10 => 7 | 11 => 11

/-! ### Integer matrix verifications via decide -/

lemma a4MatZ_mul (i j : Fin 12) : a4MatZ i * a4MatZ j = a4MatZ (a4MulTable i j) := by
  fin_cases i <;> fin_cases j <;> decide

lemma a4MatZ_orth (k : Fin 12) : (a4MatZ k).transpose * a4MatZ k = 1 := by
  fin_cases k <;> decide

lemma a4MatZ_pow_six (i : Fin 12) : a4MatZ i ^ 6 = 1 := by
  fin_cases i <;> decide

lemma a4MatZ_order_le3 (i : Fin 12) : a4MatZ i ^ 2 = 1 ∨ a4MatZ i ^ 3 = 1 := by
  fin_cases i <;> simp <;> decide

lemma a4MatZ_injective : Function.Injective a4MatZ := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; revert hab; decide)

lemma a4InvTable_mul (i : Fin 12) : a4MulTable (a4InvTable i) i = 0 := by
  fin_cases i <;> decide

/-! ### Transfer to real matrices -/

lemma a4MatZ_zero : a4MatZ 0 = 1 := by decide

lemma a4Mat_mul (i j : Fin 12) : a4Mat i * a4Mat j = a4Mat (a4MulTable i j) := by
  unfold a4Mat; rw [← toReal_mul, a4MatZ_mul]

lemma a4Mat_one : a4Mat 0 = 1 := by
  unfold a4Mat; rw [a4MatZ_zero, toReal_one]

lemma a4Mat_mem_O3 (k : Fin 12) : a4Mat k ∈ orthogonalGroup (Fin 3) ℝ := by
  rw [mem_orthogonalGroup_iff']
  show (toReal (a4MatZ k)).transpose * toReal (a4MatZ k) = 1
  rw [← toReal_transpose, ← toReal_mul, a4MatZ_orth, toReal_one]

lemma a4Mat_pow_six (i : Fin 12) : a4Mat i ^ 6 = 1 := by
  show toReal (a4MatZ i) ^ 6 = 1
  rw [← toReal_pow, a4MatZ_pow_six, toReal_one]

lemma a4Mat_order_le3 (i : Fin 12) : a4Mat i ^ 2 = 1 ∨ a4Mat i ^ 3 = 1 := by
  rcases a4MatZ_order_le3 i with h | h
  · left; show toReal (a4MatZ i) ^ 2 = 1; rw [← toReal_pow, h, toReal_one]
  · right; show toReal (a4MatZ i) ^ 3 = 1; rw [← toReal_pow, h, toReal_one]

lemma a4Mat_injective : Function.Injective a4Mat := by
  exact toReal_injective.comp a4MatZ_injective

/-! ### Constructing the SpaceIsometry subgroup -/

lemma multiplication_eq_hom' (A : O3) : multiplication A = multiplicationHom A := rfl

noncomputable def a4Elem (k : Fin 12) : SpaceIsometry :=
  multiplication ⟨a4Mat k, a4Mat_mem_O3 k⟩

lemma a4Elem_injective : Function.Injective a4Elem := by
  intro a b hab
  apply a4Mat_injective
  exact congrArg Subtype.val (multiplicationHom_injective hab)

lemma a4Elem_mul (i j : Fin 12) : a4Elem i * a4Elem j = a4Elem (a4MulTable i j) := by
  simp only [a4Elem, multiplication_eq_hom', ← map_mul]
  congr 1; exact Subtype.ext (a4Mat_mul i j)

lemma a4Elem_one : a4Elem 0 = 1 := by
  simp only [a4Elem, multiplication_eq_hom']
  have h : (⟨a4Mat 0, a4Mat_mem_O3 0⟩ : O3) = 1 := Subtype.ext a4Mat_one
  rw [h]; exact map_one multiplicationHom

def tetrahedralSubgroup : Subgroup SpaceIsometry where
  carrier := Set.range a4Elem
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨a4MulTable i j, (a4Elem_mul i j).symm⟩
  one_mem' := ⟨0, a4Elem_one⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨a4InvTable i, ?_⟩
    have hmul : a4Elem (a4InvTable i) * a4Elem i = 1 := by
      rw [a4Elem_mul]
      have h0 : a4MulTable (a4InvTable i) i = 0 := by fin_cases i <;> rfl
      rw [h0]; exact a4Elem_one
    rw [eq_comm, inv_eq_of_mul_eq_one_left hmul]

/-! ### Cardinality -/

lemma card_tetrahedralSubgroup : Nat.card tetrahedralSubgroup = 12 := by
  change Nat.card (Set.range a4Elem) = 12
  rw [Nat.card_congr (Equiv.ofInjective a4Elem a4Elem_injective).symm]
  simp

/-! ### Exponent and element orders in the subgroup -/

lemma multiplication_eq_hom (A : O3) : multiplication A = multiplicationHom A := rfl

lemma multiplication_pow (A : O3) (n : ℕ) : multiplication A ^ n = multiplication (A ^ n) := by
  simp only [multiplication_eq_hom, map_pow]

private lemma a4Elem_pow_n_eq_one {i : Fin 12} {n : ℕ} (h : a4Mat i ^ n = 1) :
    a4Elem i ^ n = 1 := by
  unfold a4Elem; rw [multiplication_pow]
  have : (⟨a4Mat i, a4Mat_mem_O3 i⟩ : O3) ^ n = 1 := Subtype.ext h
  rw [this]; exact multiplicationHom.map_one

private lemma forall_a4Elem (P : tetrahedralSubgroup → Prop)
    (h : ∀ i : Fin 12, P ⟨a4Elem i, ⟨i, rfl⟩⟩) : ∀ g, P g := by
  intro g
  obtain ⟨i, hi⟩ := g.prop
  have : g = ⟨a4Elem i, ⟨i, rfl⟩⟩ := Subtype.ext hi.symm
  rw [this]; exact h i

private lemma a4Elem_subgroup_pow_eq_one {i : Fin 12} {n : ℕ} (h : a4Mat i ^ n = 1) :
    (⟨a4Elem i, ⟨i, rfl⟩⟩ : tetrahedralSubgroup) ^ n = 1 := by
  apply Subtype.ext
  show (a4Elem i) ^ n = (1 : tetrahedralSubgroup).val
  simp only [OneMemClass.coe_one]
  exact a4Elem_pow_n_eq_one h

lemma tetrahedralSubgroup_pow_six (g : tetrahedralSubgroup) : g ^ 6 = 1 :=
  forall_a4Elem (fun g => g ^ 6 = 1) (fun i => a4Elem_subgroup_pow_eq_one (a4Mat_pow_six i)) g

lemma tetrahedralSubgroup_order_divides (g : tetrahedralSubgroup) :
    g ^ 2 = 1 ∨ g ^ 3 = 1 :=
  forall_a4Elem (fun g => g ^ 2 = 1 ∨ g ^ 3 = 1) (fun i => by
    rcases a4Mat_order_le3 i with h | h
    · left; exact a4Elem_subgroup_pow_eq_one h
    · right; exact a4Elem_subgroup_pow_eq_one h) g

lemma tetrahedralSubgroup_exponent_dvd_six : Monoid.exponent tetrahedralSubgroup ∣ 6 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one tetrahedralSubgroup_pow_six

/-! ### Not cyclic -/

lemma tetrahedralSubgroup_not_cyclic : ¬ IsCyclic tetrahedralSubgroup := by
  intro hcyc
  have hexp := @IsCyclic.exponent_eq_card _ _ hcyc
  rw [card_tetrahedralSubgroup] at hexp
  have h6 := tetrahedralSubgroup_exponent_dvd_six
  rw [hexp] at h6; omega

/-! ### Not dihedral -/

lemma tetrahedralSubgroup_no_order_six (g : tetrahedralSubgroup) : orderOf g ≠ 6 := by
  intro h6
  rcases tetrahedralSubgroup_order_divides g with h2 | h3
  · have := orderOf_dvd_of_pow_eq_one h2; rw [h6] at this; omega
  · have := orderOf_dvd_of_pow_eq_one h3; rw [h6] at this; omega

lemma tetrahedralSubgroup_not_dihedral : ¬ IsDihedral tetrahedralSubgroup := by
  intro ⟨n, ⟨e⟩⟩
  have hcard : Nat.card (DihedralGroup n) = 12 := by
    rw [← card_tetrahedralSubgroup, Nat.card_congr e.toEquiv]
  rw [DihedralGroup.nat_card] at hcard
  have hn : n = 6 := by omega
  subst hn
  have hr : orderOf (DihedralGroup.r (1 : ZMod 6)) = 6 := DihedralGroup.orderOf_r_one
  have := e.orderOf_eq (DihedralGroup.r 1)
  rw [hr] at this
  exact tetrahedralSubgroup_no_order_six (e (DihedralGroup.r 1)) this

/-! ### Main results -/

lemma tetrahedralSubgroup_isExceptional : IsExceptional tetrahedralSubgroup :=
  ⟨tetrahedralSubgroup_not_cyclic, tetrahedralSubgroup_not_dihedral,
   by rw [card_tetrahedralSubgroup]; omega⟩

theorem SpaceIsometry.existsExceptionalOfOrder12 (n : ℕ) [NeZero n]
    : ∃ f : Subgroup SpaceIsometry, IsExceptional f ∧ Nat.card f = 12 :=
  ⟨tetrahedralSubgroup, tetrahedralSubgroup_isExceptional, card_tetrahedralSubgroup⟩

theorem SpaceIsometry.existsExceptional (n : ℕ) [NeZero n]
    : ∃ f : Subgroup SpaceIsometry, IsExceptional f :=
  ⟨tetrahedralSubgroup, tetrahedralSubgroup_isExceptional⟩

theorem SpaceIsometry.existsExceptionalOfOrder24 (n : ℕ) [NeZero n]
    : ∃ f : Subgroup SpaceIsometry, IsExceptional f ∧ Nat.card f = 24 := by
  sorry

theorem SpaceIsometry.existsExceptionalOfOrder60 (n : ℕ) [NeZero n]
    : ∃ f : Subgroup SpaceIsometry, IsExceptional f ∧ Nat.card f = 60 := by
  sorry
