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
  ∀ x ∈ A, ∀ y ∈ A, ∀ ε > 0, ∃ δ > 0, MX.d x y < δ → MY.d (f x) (f y) < ε

abbrev I01 := Set.Icc (0:ℝ) 1

/--
The class of C^k functions on [0, 1], where k is a natural number.

We represent this as a function from ℝ to ℝ that is ContDiff(k) on unitInterval, where "ContDiff on" means `ContDiffOn`, and which are zero outside the unit interval.
-/
@[ext]
structure UnitIntervalC (k : ℕ) where
  toFun : ℝ → ℝ
  contDiff : ContDiffOn ℝ k toFun unitInterval
  vanishesOutside : ∀ x ∉ unitInterval, toFun x = 0

@[fun_prop]
lemma UnitIntervalC.contDiffOn (k : ℕ) (u : UnitIntervalC k) : ContDiffOn ℝ k u.toFun unitInterval := u.contDiff

/-
Example 11 - Metric on continuous functions on [0, 1]
-/

noncomputable def d_sup {k : ℕ} (f g : UnitIntervalC k) : ℝ :=
  ⨆ x : unitInterval, |f.toFun x - g.toFun x|

attribute [fun_prop] ContinuousOn.restrict

private lemma d_sup_bddAbove {k : ℕ} (f g : UnitIntervalC k) :
    BddAbove (Set.range fun x : unitInterval => |f.toFun x - g.toFun x|) := by
  have : CompactSpace unitInterval := isCompact_iff_compactSpace.mp isCompact_Icc
  apply IsCompact.bddAbove
  apply isCompact_range
  exact ((f.contDiff.continuousOn.sub g.contDiff.continuousOn).abs).restrict

private lemma le_d_sup {k : ℕ} (f g : UnitIntervalC k) (x : ↥unitInterval) :
    |f.toFun ↑x - g.toFun ↑x| ≤ d_sup f g :=
  le_ciSup (d_sup_bddAbove f g) x

lemma d_sup_symm {k : ℕ} (f g : UnitIntervalC k) : d_sup f g = d_sup g f := by
  simp only [d_sup]
  simp [abs_sub_comm]

lemma d_sup_nonneg {k : ℕ} (f g : UnitIntervalC k) : 0 ≤ d_sup f g := by
  simp [d_sup, Real.iSup_nonneg]

lemma d_sup_triangle {k : ℕ} (f g h : UnitIntervalC k) : d_sup f h ≤ d_sup f g + d_sup g h := by
  simp only [d_sup]
  apply ciSup_le
  intro x
  calc |f.toFun ↑x - h.toFun ↑x|
      = |(f.toFun ↑x - g.toFun ↑x) + (g.toFun ↑x - h.toFun ↑x)| := by ring_nf
    _ ≤ |f.toFun ↑x - g.toFun ↑x| + |g.toFun ↑x - h.toFun ↑x| := abs_add_le _ _
    _ ≤ d_sup f g + d_sup g h := add_le_add (le_d_sup f g x) (le_d_sup g h x)

noncomputable def SupMetric0 : IMetricSpace (UnitIntervalC 0) where -- the sup metric on C^0 functions on [0,1]
  d := d_sup
  d_nonneg := d_sup_nonneg
  d_zero_iff_eq f g := by
    simp only [d_sup]
    constructor
    · intro h
      have hbdd := d_sup_bddAbove f g
      ext x
      by_cases hx : x ∈ unitInterval
      · have hle : |f.toFun x - g.toFun x| ≤ 0 :=
          calc |f.toFun x - g.toFun x|
              ≤ ⨆ y : ↥unitInterval, |f.toFun ↑y - g.toFun ↑y| :=
                le_ciSup hbdd ⟨x, hx⟩
            _ = 0 := h
        exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)
      · rw [f.vanishesOutside x hx, g.vanishesOutside x hx]
    · intro h
      subst h
      simp
  d_symm := d_sup_symm
  d_triangle := d_sup_triangle

/-
Example 14
-/



noncomputable def UnitIntervalC.deriv {k : ℕ} (f : UnitIntervalC (k + 1)) : (UnitIntervalC k) where
  toFun := fun x => derivWithin f.toFun unitInterval x
  contDiff := f.contDiff.derivWithin uniqueDiffOn_Icc_zero_one (by norm_cast)
  vanishesOutside := by
    intro x hx
    apply derivWithin_zero_of_notMem_closure
    rwa [closure_Icc]

noncomputable def d_sup_add_deriv (f g : UnitIntervalC 1) : ℝ := d_sup f g + d_sup (UnitIntervalC.deriv f) (UnitIntervalC.deriv g)

noncomputable def GraphMetric1 : IMetricSpace (UnitIntervalC 1) where
  d := d_sup_add_deriv
  d_nonneg f g := by
    simp [d_sup_add_deriv]
    linarith [d_sup_nonneg f g, d_sup_nonneg f.deriv g.deriv]
  d_zero_iff_eq f g := by
    constructor
    · intro h
      simp only [d_sup_add_deriv] at h
      have h1 : 0 ≤ d_sup f g := by exact d_sup_nonneg f g
      have h2 : 0 ≤ d_sup (UnitIntervalC.deriv f) (UnitIntervalC.deriv g) := by exact d_sup_nonneg f.deriv g.deriv
      have h_sup : d_sup f g = 0 := by linarith
      ext x
      by_cases hx : x ∈ unitInterval
      · by_contra hne
        unfold d_sup at h_sup
        have h' : 0 < |f.toFun x - g.toFun x| := by grind
        have hle := le_ciSup (d_sup_bddAbove f g) ⟨x, hx⟩
        rw [h_sup] at hle
        linarith
      · rw [f.vanishesOutside x hx, g.vanishesOutside x hx]
    · rintro rfl
      simp [d_sup_add_deriv, d_sup]
  d_symm f g := by
    simp [d_sup_add_deriv, d_sup_symm]
  d_triangle f g h := by
    simp [d_sup_add_deriv]
    have h1 := d_sup_triangle f g h
    have h2 := d_sup_triangle f.deriv g.deriv h.deriv
    linarith

/-- x · 𝟙_{[0,1]} as a C¹ function on [0,1] that vanishes outside. -/
noncomputable def xIndicator : UnitIntervalC 1 where
  toFun := fun x => x * Set.indicator unitInterval 1 x
  contDiff := contDiffOn_id.congr fun x hx => by simp [Set.indicator_of_mem hx]
  vanishesOutside := by
    intro x hx
    simp [Set.indicator, hx]

-- Helper: f agrees with 0 outside unitInterval
private lemma xInd_eq_zero {y : ℝ} (hy : y ∉ unitInterval) :
    y * Set.indicator unitInterval 1 y = 0 := by
  simp [Set.indicator_of_notMem hy]

-- Helper: f agrees with id inside unitInterval
private lemma xInd_eq_id {y : ℝ} (hy : y ∈ unitInterval) :
    y * Set.indicator unitInterval 1 y = y := by
  simp [Set.indicator_of_mem hy]

/-- The derivWithin of x · 𝟙_{[0,1]} on [0,1] equals 1 on [0,1]. -/
theorem xIndicator_deriv :
    Set.EqOn (UnitIntervalC.deriv xIndicator).toFun (fun _ => 1) unitInterval := by
  set f := fun x : ℝ => x * Set.indicator unitInterval 1 x with hf_def
  have hf_id : ∀ y, y ∈ unitInterval → f y = y := fun y hy => xInd_eq_id hy
  intro x hx
  simp only [UnitIntervalC.deriv, xIndicator]
  have huniq : UniqueDiffWithinAt ℝ unitInterval x := by
    apply UniqueDiffOn.uniqueDiffWithinAt _ hx
    exact uniqueDiffOn_Icc_zero_one
  have : derivWithin f unitInterval x = derivWithin id unitInterval x :=
    derivWithin_congr (fun y hy => hf_id y hy) (hf_id x hx)
  rw [this, derivWithin_id _ _ huniq]

/-
Example 16
-/

example : IsContinuous GraphMetric1 SupMetric0 UnitIntervalC.deriv ⊤ := by
  intro f _ g _ ε hε
  use ε, hε
  intro h
  dsimp [GraphMetric1, d_sup_add_deriv] at h
  dsimp [SupMetric0]
  linarith [d_sup_nonneg f g]

/-
Example 18 - Geodesic - deliberately omitted
-/


/-
Example 19 - Trivial metric
-/

def TrivialMetric {X : Type} [DecidableEq X] : IMetricSpace X where
  d := fun x y => if x = y then 0 else 1
  d_nonneg x y := by grind
  d_zero_iff_eq x y := by grind
  d_symm x y := by grind
  d_triangle x y z := by grind

noncomputable def integral01 (f : ℝ → ℝ) : ℝ :=
  ∫ x in 0..1, |f x|

noncomputable def integral01' (f g : UnitIntervalC 0) : ℝ :=
  integral01 (fun x => |f.toFun x - g.toFun x|)

attribute [gcongr] intervalIntegral.integral_mono_on

lemma integral01'_nonneg (f g : UnitIntervalC 0) : 0 ≤ integral01' f g := by
  unfold integral01' integral01
  nth_rw 1 [show (0:ℝ) = ∫ _ in (0:ℝ)..1, (0:ℝ) by simp]
  gcongr with x hx
  · exact intervalIntegrable_const
  · exact (((f.contDiff.continuousOn.sub g.contDiff.continuousOn).abs).abs).intervalIntegrable_of_Icc (by norm_num)
  · positivity

lemma integral01'_symm (f g : UnitIntervalC 0) : integral01' f g = integral01' g f := by
  dsimp [integral01', integral01]
  grind [abs_sub_comm]

lemma integral01'_triangle_aux (f g h : UnitIntervalC 0) :
    ∫ x in (0:ℝ)..1, |(|f.toFun x - h.toFun x|)| ≤
    ∫ x in (0:ℝ)..1, (|(|f.toFun x - g.toFun x|)| + |(|g.toFun x - h.toFun x|)|) := by
  gcongr with x hx
  · exact (((f.contDiff.continuousOn.sub h.contDiff.continuousOn).abs).abs).intervalIntegrable_of_Icc (by norm_num)
  · exact ((((f.contDiff.continuousOn.sub g.contDiff.continuousOn).abs).abs).intervalIntegrable_of_Icc (by norm_num)).add
          ((((g.contDiff.continuousOn.sub h.contDiff.continuousOn).abs).abs).intervalIntegrable_of_Icc (by norm_num))
  · grind [abs_add_le]

attribute [fun_prop] IntervalIntegrable
attribute [fun_prop] IntervalIntegrable.abs IntervalIntegrable.sub IntervalIntegrable.add IntervalIntegrable.neg
attribute [fun_prop] ContinuousOn.intervalIntegrable_of_Icc

lemma intervalIntegrable_abs_abs_sub {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1)) :
    IntervalIntegrable (fun x => |(|f x - g x|)|) MeasureTheory.volume 0 1 := by
  fun_prop (disch := norm_num)

lemma integral01'_intervalIntegrable (f g : UnitIntervalC 0) :
    IntervalIntegrable (fun x => |(|f.toFun x - g.toFun x|)|) MeasureTheory.volume 0 1 :=
  intervalIntegrable_abs_abs_sub f.contDiff.continuousOn g.contDiff.continuousOn

lemma integral01'_triangle (f g h : UnitIntervalC 0) : integral01' f h ≤ integral01' f g + integral01' g h := by
  dsimp [integral01', integral01]
  rw [← intervalIntegral.integral_add
        (integral01'_intervalIntegrable f g) (integral01'_intervalIntegrable g h)]
  exact integral01'_triangle_aux f g h

/-
Example 21 - L1 metric
-/
noncomputable def L1Metric : IMetricSpace (UnitIntervalC 0) where
  d := integral01'
  d_nonneg := integral01'_nonneg
  d_zero_iff_eq := sorry
  d_symm := integral01'_symm
  d_triangle := integral01'_triangle
