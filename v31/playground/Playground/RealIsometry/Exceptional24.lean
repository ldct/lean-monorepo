import Playground.RealIsometry.Basic
import Playground.RealIsometry.Dihedral

set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option linter.style.show false
set_option linter.flexible false

open Matrix

abbrev IsDihedral (G : Type*) [Group G] : Prop := ∃ n : ℕ, Nonempty (DihedralGroup n ≃* G)

def IsExceptional (H : Subgroup SpaceIsometry) : Prop :=
  ¬ IsCyclic H ∧ ¬ IsDihedral H ∧ Nat.card H ≠ 0

/-! ## Chiral octahedral group (S₄) as a subgroup of RealIsometry

We realize S₄ as the group of 24 signed permutation matrices in O(3) with determinant +1.
These are the rotation symmetries of a cube (or regular octahedron).

Element orders: 1 appears 1×, 2 appears 9×, 3 appears 8×, 4 appears 6×.
The exponent (lcm of orders) is 12.
-/

/-! ### Integer matrices and casting infrastructure -/

abbrev IMAT3 := Matrix (Fin 3) (Fin 3) ℤ

abbrev Matrix.toReal (M : IMAT3) : MAT3 := M.map (Int.castRingHom ℝ)

lemma toReal_mul (A B : IMAT3) : (A * B).toReal = A.toReal * B.toReal := by
  grind [Matrix.map_mul]

lemma toReal_one : toReal 1 = (1 : MAT3) := by simp

lemma toReal_pow (A : IMAT3) (n : ℕ) : toReal (A ^ n) = (toReal A) ^ n := by
  induction n with
  | zero => simp [pow_zero]
  | succ n IH => rw [pow_succ, toReal_mul, IH, pow_succ]

lemma toReal_injective : Function.Injective toReal := by
  apply Matrix.map_injective
  exact RingHom.injective_int _

lemma toReal_transpose (A : IMAT3) : toReal A.transpose = (toReal A).transpose := by
  ext i j; simp [toReal, map_apply, transpose_apply]

/-! ### The 24 integer matrices of the chiral octahedral group -/

def s4MatZ : Fin 24 → IMAT3 := ![
  !![1, 0, 0; 0, 1, 0; 0, 0, 1],
  !![0, 0, 1; 1, 0, 0; 0, 1, 0],
  !![0, 1, 0; 0, 0, 1; 1, 0, 0],
  !![1, 0, 0; 0, -1, 0; 0, 0, -1],
  !![0, 1, 0; 0, 0, -1; -1, 0, 0],
  !![0, 0, 1; -1, 0, 0; 0, -1, 0],
  !![0, 0, -1; 1, 0, 0; 0, -1, 0],
  !![0, -1, 0; 0, 0, 1; -1, 0, 0],
  !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
  !![0, -1, 0; 0, 0, -1; 1, 0, 0],
  !![0, 0, -1; -1, 0, 0; 0, 1, 0],
  !![-1, 0, 0; 0, -1, 0; 0, 0, 1],
  !![-1, 0, 0; 0, 0, -1; 0, -1, 0],
  !![-1, 0, 0; 0, 0, 1; 0, 1, 0],
  !![1, 0, 0; 0, 0, -1; 0, 1, 0],
  !![1, 0, 0; 0, 0, 1; 0, -1, 0],
  !![0, -1, 0; -1, 0, 0; 0, 0, -1],
  !![0, -1, 0; 1, 0, 0; 0, 0, 1],
  !![0, 1, 0; -1, 0, 0; 0, 0, 1],
  !![0, 1, 0; 1, 0, 0; 0, 0, -1],
  !![0, 0, -1; 0, -1, 0; -1, 0, 0],
  !![0, 0, -1; 0, 1, 0; 1, 0, 0],
  !![0, 0, 1; 0, -1, 0; 1, 0, 0],
  !![0, 0, 1; 0, 1, 0; -1, 0, 0]
]

def s4Mat (k : Fin 24) : MAT3 := toReal (s4MatZ k)

/-! ### Multiplication table -/

def s4MulTable : Fin 24 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![1, 2, 0, 6, 8, 7, 9, 11, 10, 3, 4, 5, 16, 18, 19, 17, 20, 22, 23, 21, 12, 14, 15, 13],
  ![2, 0, 1, 9, 10, 11, 3, 5, 4, 6, 8, 7, 20, 23, 21, 22, 12, 15, 13, 14, 16, 19, 17, 18],
  ![3, 5, 4, 0, 2, 1, 10, 9, 11, 7, 6, 8, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22],
  ![4, 3, 5, 7, 6, 8, 0, 1, 2, 10, 11, 9, 21, 22, 20, 23, 13, 14, 12, 15, 17, 18, 16, 19],
  ![5, 4, 3, 10, 11, 9, 7, 8, 6, 0, 2, 1, 17, 19, 18, 16, 21, 23, 22, 20, 13, 15, 14, 12],
  ![6, 7, 8, 1, 0, 2, 4, 3, 5, 11, 9, 10, 18, 16, 17, 19, 22, 20, 21, 23, 14, 12, 13, 15],
  ![7, 8, 6, 4, 5, 3, 11, 10, 9, 1, 0, 2, 22, 21, 23, 20, 14, 13, 15, 12, 18, 17, 19, 16],
  ![8, 6, 7, 11, 9, 10, 1, 2, 0, 4, 5, 3, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21],
  ![9, 11, 10, 2, 1, 0, 8, 6, 7, 5, 3, 4, 23, 20, 22, 21, 15, 12, 14, 13, 19, 16, 18, 17],
  ![10, 9, 11, 5, 3, 4, 2, 0, 1, 8, 7, 6, 19, 17, 16, 18, 23, 21, 20, 22, 15, 13, 12, 14],
  ![11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20],
  ![12, 20, 16, 13, 17, 21, 23, 19, 15, 18, 22, 14, 0, 3, 11, 8, 2, 4, 9, 7, 1, 5, 10, 6],
  ![13, 21, 17, 12, 16, 20, 22, 18, 14, 19, 23, 15, 3, 0, 8, 11, 4, 2, 7, 9, 5, 1, 6, 10],
  ![14, 22, 18, 15, 19, 23, 21, 17, 13, 16, 20, 12, 8, 11, 3, 0, 7, 9, 4, 2, 6, 10, 5, 1],
  ![15, 23, 19, 14, 18, 22, 20, 16, 12, 17, 21, 13, 11, 8, 0, 3, 9, 7, 2, 4, 10, 6, 1, 5],
  ![16, 12, 20, 18, 22, 14, 13, 21, 17, 23, 15, 19, 1, 6, 5, 10, 0, 8, 3, 11, 2, 7, 4, 9],
  ![17, 13, 21, 19, 23, 15, 12, 20, 16, 22, 14, 18, 5, 10, 1, 6, 3, 11, 0, 8, 4, 9, 2, 7],
  ![18, 14, 22, 16, 20, 12, 15, 23, 19, 21, 13, 17, 6, 1, 10, 5, 8, 0, 11, 3, 7, 2, 9, 4],
  ![19, 15, 23, 17, 21, 13, 14, 22, 18, 20, 12, 16, 10, 5, 6, 1, 11, 3, 8, 0, 9, 4, 7, 2],
  ![20, 16, 12, 23, 15, 19, 18, 14, 22, 13, 17, 21, 2, 9, 7, 4, 1, 10, 6, 5, 0, 11, 8, 3],
  ![21, 17, 13, 22, 14, 18, 19, 15, 23, 12, 16, 20, 4, 7, 9, 2, 5, 6, 10, 1, 3, 8, 11, 0],
  ![22, 18, 14, 21, 13, 17, 16, 12, 20, 15, 19, 23, 7, 4, 2, 9, 6, 5, 1, 10, 8, 3, 0, 11],
  ![23, 19, 15, 20, 12, 16, 17, 13, 21, 14, 18, 22, 9, 2, 4, 7, 10, 1, 5, 6, 11, 0, 3, 8]
]

def s4InvTable : Fin 24 → Fin 24 :=
  ![0, 2, 1, 3, 6, 9, 4, 10, 8, 5, 7, 11, 12, 13, 15, 14, 16, 18, 17, 19, 20, 23, 22, 21]

/-! ### Integer matrix verifications via native_decide -/

lemma s4MatZ_mul (i j : Fin 24) : s4MatZ i * s4MatZ j = s4MatZ (s4MulTable i j) := by
  fin_cases i <;> fin_cases j <;> native_decide

lemma s4MatZ_orth (k : Fin 24) : (s4MatZ k).transpose * s4MatZ k = 1 := by
  fin_cases k <;> native_decide

lemma s4MatZ_pow_twelve (i : Fin 24) : s4MatZ i ^ 12 = 1 := by
  fin_cases i <;> native_decide

lemma s4MatZ_order_le4 (i : Fin 24) :
    s4MatZ i ^ 2 = 1 ∨ s4MatZ i ^ 3 = 1 ∨ s4MatZ i ^ 4 = 1 := by
  fin_cases i <;> simp <;> native_decide

lemma s4MatZ_injective : Function.Injective s4MatZ := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; revert hab; native_decide)

lemma s4InvTable_mul (i : Fin 24) : s4MulTable (s4InvTable i) i = 0 := by
  fin_cases i <;> native_decide

/-! ### Transfer to real matrices -/

lemma s4MatZ_zero : s4MatZ 0 = 1 := by native_decide

lemma s4Mat_mul (i j : Fin 24) : s4Mat i * s4Mat j = s4Mat (s4MulTable i j) := by
  unfold s4Mat; rw [← toReal_mul, s4MatZ_mul]

lemma s4Mat_one : s4Mat 0 = 1 := by
  unfold s4Mat; rw [s4MatZ_zero, toReal_one]

lemma s4Mat_mem_O3 (k : Fin 24) : s4Mat k ∈ orthogonalGroup (Fin 3) ℝ := by
  rw [mem_orthogonalGroup_iff']
  change (toReal (s4MatZ k)).transpose * toReal (s4MatZ k) = 1
  rw [← toReal_transpose, ← toReal_mul, s4MatZ_orth, toReal_one]

lemma s4Mat_pow_twelve (i : Fin 24) : s4Mat i ^ 12 = 1 := by
  change toReal (s4MatZ i) ^ 12 = 1
  rw [← toReal_pow, s4MatZ_pow_twelve, toReal_one]

lemma s4Mat_order_le4 (i : Fin 24) :
    s4Mat i ^ 2 = 1 ∨ s4Mat i ^ 3 = 1 ∨ s4Mat i ^ 4 = 1 := by
  rcases s4MatZ_order_le4 i with h | h | h
  · left; change toReal (s4MatZ i) ^ 2 = 1; rw [← toReal_pow, h, toReal_one]
  · right; left; change toReal (s4MatZ i) ^ 3 = 1; rw [← toReal_pow, h, toReal_one]
  · right; right; change toReal (s4MatZ i) ^ 4 = 1; rw [← toReal_pow, h, toReal_one]

lemma s4Mat_injective : Function.Injective s4Mat := toReal_injective.comp s4MatZ_injective

/-! ### Constructing the SpaceIsometry subgroup -/

lemma multiplication_eq_hom' (A : O3) : multiplication A = multiplicationHom A := rfl

noncomputable def s4Elem (k : Fin 24) : SpaceIsometry :=
  multiplication ⟨s4Mat k, s4Mat_mem_O3 k⟩

lemma s4Elem_injective : Function.Injective s4Elem := by
  intro a b hab
  apply s4Mat_injective
  exact congrArg Subtype.val (multiplicationHom_injective hab)

lemma s4Elem_mul (i j : Fin 24) : s4Elem i * s4Elem j = s4Elem (s4MulTable i j) := by
  simp only [s4Elem, multiplication_eq_hom', ← map_mul]
  congr 1; exact Subtype.ext (s4Mat_mul i j)

lemma s4Elem_one : s4Elem 0 = 1 := by
  simp only [s4Elem, multiplication_eq_hom']
  have h : (⟨s4Mat 0, s4Mat_mem_O3 0⟩ : O3) = 1 := Subtype.ext s4Mat_one
  rw [h]; exact map_one multiplicationHom

def chiralOctahedralSubgroup : Subgroup SpaceIsometry where
  carrier := Set.range s4Elem
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨s4MulTable i j, (s4Elem_mul i j).symm⟩
  one_mem' := ⟨0, s4Elem_one⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨s4InvTable i, ?_⟩
    have hmul : s4Elem (s4InvTable i) * s4Elem i = 1 := by
      rw [s4Elem_mul]
      have h0 : s4MulTable (s4InvTable i) i = 0 := s4InvTable_mul i
      rw [h0]; exact s4Elem_one
    rw [eq_comm, inv_eq_of_mul_eq_one_left hmul]

/-! ### Cardinality -/

lemma card_chiralOctahedralSubgroup : Nat.card chiralOctahedralSubgroup = 24 := by
  change Nat.card (Set.range s4Elem) = 24
  simp [Nat.card_congr (Equiv.ofInjective s4Elem s4Elem_injective).symm]

/-! ### Exponent and element orders in the subgroup -/

lemma multiplication_pow (A : O3) (n : ℕ) : multiplication A ^ n = multiplication (A ^ n) := by
  simp only [multiplication_eq_hom', map_pow]

private lemma s4Elem_pow_n_eq_one {i : Fin 24} {n : ℕ} (h : s4Mat i ^ n = 1) :
    s4Elem i ^ n = 1 := by
  unfold s4Elem; rw [multiplication_pow]
  have : (⟨s4Mat i, s4Mat_mem_O3 i⟩ : O3) ^ n = 1 := Subtype.ext h
  rw [this]; exact multiplicationHom.map_one

private lemma forall_s4Elem (P : chiralOctahedralSubgroup → Prop)
    (h : ∀ i : Fin 24, P ⟨s4Elem i, ⟨i, rfl⟩⟩) : ∀ g, P g := by
  intro g
  obtain ⟨i, hi⟩ := g.prop
  have : g = ⟨s4Elem i, ⟨i, rfl⟩⟩ := Subtype.ext hi.symm
  rw [this]; exact h i

private lemma s4Elem_subgroup_pow_eq_one {i : Fin 24} {n : ℕ} (h : s4Mat i ^ n = 1) :
    (⟨s4Elem i, ⟨i, rfl⟩⟩ : chiralOctahedralSubgroup) ^ n = 1 := by
  apply Subtype.ext
  change (s4Elem i) ^ n = (1 : chiralOctahedralSubgroup).val
  simp only [OneMemClass.coe_one]
  exact s4Elem_pow_n_eq_one h

lemma chiralOctahedralSubgroup_pow_twelve (g : chiralOctahedralSubgroup) : g ^ 12 = 1 :=
  forall_s4Elem (fun g => g ^ 12 = 1)
    (fun i => s4Elem_subgroup_pow_eq_one (s4Mat_pow_twelve i)) g

lemma chiralOctahedralSubgroup_order_divides (g : chiralOctahedralSubgroup) :
    g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 :=
  forall_s4Elem (fun g => g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1) (fun i => by
    rcases s4Mat_order_le4 i with h | h | h
    · left; exact s4Elem_subgroup_pow_eq_one h
    · right; left; exact s4Elem_subgroup_pow_eq_one h
    · right; right; exact s4Elem_subgroup_pow_eq_one h) g

lemma chiralOctahedralSubgroup_exponent_dvd_twelve :
    Monoid.exponent chiralOctahedralSubgroup ∣ 12 :=
  Monoid.exponent_dvd_of_forall_pow_eq_one chiralOctahedralSubgroup_pow_twelve

/-! ### Not cyclic -/

lemma chiralOctahedralSubgroup_not_cyclic : ¬ IsCyclic chiralOctahedralSubgroup := by
  intro hcyc
  have hexp := @IsCyclic.exponent_eq_card _ _ hcyc
  rw [card_chiralOctahedralSubgroup] at hexp
  have h12 := chiralOctahedralSubgroup_exponent_dvd_twelve
  rw [hexp] at h12; omega

/-! ### Not dihedral -/

lemma chiralOctahedralSubgroup_no_order_twelve (g : chiralOctahedralSubgroup) :
    orderOf g ≠ 12 := by
  intro h12
  rcases chiralOctahedralSubgroup_order_divides g with h2 | h3 | h4
  · have := orderOf_dvd_of_pow_eq_one h2; rw [h12] at this; omega
  · have := orderOf_dvd_of_pow_eq_one h3; rw [h12] at this; omega
  · have := orderOf_dvd_of_pow_eq_one h4; rw [h12] at this; omega

lemma chiralOctahedralSubgroup_not_dihedral : ¬ IsDihedral chiralOctahedralSubgroup := by
  intro ⟨n, ⟨e⟩⟩
  have hcard : Nat.card (DihedralGroup n) = 24 := by
    rw [← card_chiralOctahedralSubgroup, Nat.card_congr e.toEquiv]
  rw [DihedralGroup.nat_card] at hcard
  have hn : n = 12 := by omega
  subst hn
  have hr : orderOf (DihedralGroup.r (1 : ZMod 12)) = 12 := DihedralGroup.orderOf_r_one
  have := e.orderOf_eq (DihedralGroup.r 1)
  rw [hr] at this
  exact chiralOctahedralSubgroup_no_order_twelve (e (DihedralGroup.r 1)) this

/-! ### Main result -/

lemma chiralOctahedralSubgroup_isExceptional : IsExceptional chiralOctahedralSubgroup :=
  ⟨chiralOctahedralSubgroup_not_cyclic, chiralOctahedralSubgroup_not_dihedral,
   by rw [card_chiralOctahedralSubgroup]; omega⟩

theorem SpaceIsometry.existsExceptionalOfOrder24 (n : ℕ) [NeZero n]
    : ∃ f : Subgroup SpaceIsometry, IsExceptional f ∧ Nat.card f = 24 :=
  ⟨chiralOctahedralSubgroup, chiralOctahedralSubgroup_isExceptional,
   card_chiralOctahedralSubgroup⟩
