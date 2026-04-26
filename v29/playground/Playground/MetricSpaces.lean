import Mathlib

-- https://ocw.mit.edu/courses/18-s190-introduction-to-metric-spaces-january-iap-2023/mit18_s190iap23_lec1.pdf


/- Example 2: Euclidean distance -/

abbrev 𝔼 (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev R3 := EuclideanSpace ℝ (Fin 3)

noncomputable def euclideanDistance3 (x y : R3) : ℝ :=
  ‖x - y‖

noncomputable def euclideanDistance {n : ℕ} (x y : 𝔼 n) : ℝ :=
  ‖x - y‖

lemma euclideanDistanceFormula3 (x y : R3)
: euclideanDistance3 x y = Real.sqrt ((x 1 - y 1)^2 + (x 2 - y 2)^2 + (x 3 - y 3)^2) := by
  simp [euclideanDistance3, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
  congr 1; ring

lemma euclideanDistanceFormula {n : ℕ} (x y : 𝔼 n)
: euclideanDistance x y = Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  unfold euclideanDistance
  simp [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

-- The euclidean distance is positive
example {n : ℕ} (x y : 𝔼 n) : euclideanDistance x y ≥ 0 := by
  rw [euclideanDistanceFormula]
  simp

-- The euclidean distance is zero if and only if the points are equal
example {n : ℕ} (x y : 𝔼 n) : euclideanDistance x y = 0 ↔ x = y := by
  simp only [euclideanDistanceFormula]
  constructor
  · intro h
    rw [Real.sqrt_eq_zero (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at h
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - y i))).mp h i (Finset.mem_univ i)
    nlinarith [sq_nonneg (x i - y i)]
  · intro h
    subst h
    simp

-- The euclidean distance is symmetric
example {n : ℕ} (x y : 𝔼 n) : euclideanDistance x y = euclideanDistance y x := by
  simp only [euclideanDistanceFormula]
  congr
  ext i
  grind

#check MetricSpace

/-
Definition 3 - Metric space
-/
structure IMetricSpace (X : Type) where
  d : X → X → ℝ
  d_nonneg : ∀ x y, d x y ≥ 0
  d_zero_iff_eq : ∀ x y, d x y = 0 ↔ x = y
  d_symm : ∀ x y, d x y = d y x
  d_triangle : ∀ x y z, d x z ≤ d x y + d y z

/-
Example 4 - Sup metric
-/

lemma le_sup'_univ {ι : Type*} [Fintype ι] [Nonempty ι] {α : Type*} [LinearOrder α]
    (f : ι → α) (i : ι) : f i ≤ Finset.univ.sup' Finset.univ_nonempty f :=
  Finset.le_sup' f (Finset.mem_univ i)

def d_inf {n : ℕ} [NeZero n] (x y : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |x i - y i|)

example {n : ℕ} [NeZero n] : IMetricSpace (Fin n → ℝ) where
  d := d_inf
  d_nonneg x y := by simp [d_inf]
  d_zero_iff_eq x y := by
    simp only [d_inf]
    constructor
    · intro h
      by_contra h_x_ne_y
      obtain ⟨ i, hi ⟩ := show ∃ i, x i ≠ y i by grind
      have : 0 < |x i - y i| := by grind
      have : |x i - y i| ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |x i - y i|) := by
        exact le_sup'_univ (fun j => |x j - y j|) i
      linarith
    · rintro rfl
      simp
  d_symm x y := by
    simp only [d_inf]
    congr
    ext i
    grind
  d_triangle x y z := by
    simp only [d_inf]
    apply Finset.sup'_le
    intro i _
    calc |x i - z i|
        = |(x i - y i) + (y i - z i)| := by ring_nf
      _ ≤ |x i - y i| + |y i - z i| := by grind [abs_add_le]
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |x i - y i|)
          + Finset.univ.sup' Finset.univ_nonempty (fun i => |y i - z i|) :=
        add_le_add (le_sup'_univ (fun j => |x j - y j|) i)
                   (le_sup'_univ (fun j => |y j - z j|) i)

/- Example 5 - the L1 metric -/

def d1 {n : ℕ} [NeZero n] (x y : Fin n → ℝ) : ℝ :=
  ∑ i, |x i - y i|

example (α : Type) (f g : α → ℝ) (h : ∀ i, f i ≤ g i)
: ∀ i, f i ≤ g i := by
  intro i
  exact h i
  -- exact RCLike.ofReal_le_ofReal.mp (h i) -- why is this suggested...

example {n : ℕ} [NeZero n] : IMetricSpace (Fin n → ℝ) where
  d := d1
  d_nonneg x y := by
    simp only [d1]
    positivity
  d_zero_iff_eq x y := by
    constructor
    · intro h
      simp only [d1] at h
      ext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (x i - y i))).mp h i (Finset.mem_univ i)
      linarith [abs_eq_zero.mp this]
    · rintro rfl
      simp [d1]
  d_symm x y := by
    simp only [d1]
    congr
    ext i
    grind
  d_triangle x y z := by
    simp only [d1]
    rw [← Finset.sum_add_distrib]
    gcongr with i hi
    grind [abs_add_le]

/-
Definition 7 - Convergent sequence
-/

def ConvergesTo {X : Type} (M : IMetricSpace X) (x : ℕ → X) (l : X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, M.d (x n) l ≤ ε

/-
Definition 8 - Cauchy sequence
-/

def IsCauchy {X : Type} (M : IMetricSpace X) (x : ℕ → X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, M.d (x m) (x n) ≤ ε

/-
Definition 9 - Open set
-/

def Ball {X : Type} (M : IMetricSpace X) (x : X) (ε : ℝ) : Set X :=
  { y | M.d x y < ε }

def IsIOpen {X : Type} (M : IMetricSpace X) (A : Set X) : Prop :=
  ∀ x ∈ A, ∃ ε > 0, Ball M x ε ⊆ A

/-
Definition 10 - Continuous function

maybe it's better to define continuity at a point
-/

-- The function `f` from a metric space `X` to a metric space `Y` is continuous on `A ⊆ X`
def IsContinuous {X Y : Type} (MX : IMetricSpace X) (MY : IMetricSpace Y) (f : X → Y) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ A, MX.d x y < δ → MY.d (f x) (f y) < ε

example (f : ℝ → ℝ) (hf : Continuous f) : ContDiff ℝ 0 f := by
  exact contDiff_zero.mpr hf

example (f : ℝ → ℝ) (hf : Continuous f) : ContDiff ℝ 0 f := by
  exact contDiff_zero.mpr hf

structure ContFun01 where
  toFun : ℝ → ℝ
  continuous : ContDiffOn ℝ 0 toFun (Set.Icc 0 1)

noncomputable def d01 (f g : ContFun01) : ℝ := ⨆ x ∈ Set.Icc (0:ℝ) 1, |f.toFun x - g.toFun x|

private lemma contFun01_continuousOn (f : ContFun01) :
    ContinuousOn f.toFun (Set.Icc 0 1) :=
  contDiffOn_zero.mp f.continuous

private lemma d01_bddAbove (f g : ContFun01) :
    BddAbove (Set.range fun x => ⨆ (_ : x ∈ Set.Icc (0:ℝ) 1), |f.toFun x - g.toFun x|) := by
  have hfg : ContinuousOn (fun x => |f.toFun x - g.toFun x|) (Set.Icc 0 1) :=
    ((contFun01_continuousOn f).sub (contFun01_continuousOn g)).norm
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hfg
  refine ⟨M, fun r ⟨x, hx⟩ => ?_⟩
  simp only at hx
  rw [← hx]
  by_cases hxS : x ∈ Set.Icc (0:ℝ) 1
  · rw [ciSup_pos hxS]
    exact hM (Set.mem_image_of_mem _ hxS)
  · simp only [ciSup_neg hxS, Real.sSup_empty]
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
    linarith [hM (Set.mem_image_of_mem _ h0), abs_nonneg (f.toFun 0 - g.toFun 0)]

private lemma le_d01 (f g : ContFun01) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |f.toFun x - g.toFun x| ≤ d01 f g := by
  simp only [d01]
  exact le_ciSup_of_le (d01_bddAbove f g) x
    (by rw [ciSup_pos hx])

noncomputable example : IMetricSpace ContFun01 where
  d := d01
  d_nonneg f g := by
    simp only [d01]
    exact Real.iSup_nonneg fun x => Real.iSup_nonneg fun _ => abs_nonneg _
  d_zero_iff_eq f g := by
    -- This is not provable as stated: two ContFun01 values can agree on [0,1]
    -- (making d01 = 0) but differ outside [0,1], so they are not equal as ContFun01.
    -- ContFun01 equality requires toFun to agree everywhere (ℝ → ℝ), not just on [0,1].
    sorry
  d_symm f g := by
    simp only [d01, abs_sub_comm]
  d_triangle f g h := by
    simp only [d01]
    have rhs_nonneg : 0 ≤ (⨆ x ∈ Set.Icc (0:ℝ) 1, |f.toFun x - g.toFun x|) +
        (⨆ x ∈ Set.Icc (0:ℝ) 1, |g.toFun x - h.toFun x|) :=
      add_nonneg (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _)
        (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _)
    apply Real.iSup_le (fun x => ?_) rhs_nonneg
    apply Real.iSup_le (fun hx => ?_) rhs_nonneg
    calc |f.toFun x - h.toFun x|
        = |(f.toFun x - g.toFun x) + (g.toFun x - h.toFun x)| := by ring_nf
      _ ≤ |f.toFun x - g.toFun x| + |g.toFun x - h.toFun x| := abs_add_le _ _
      _ ≤ d01 f g + d01 g h := add_le_add (le_d01 f g x hx) (le_d01 g h x hx)
