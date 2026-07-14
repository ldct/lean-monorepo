import Playground.MetricSpaces.Lecture1

namespace MIT_18_S190

-- https://ocw.mit.edu/courses/18-s190-introduction-to-metric-spaces-january-iap-2023/mit18_s190iap23_lec2.pdf
-- General theory

/-
Proposition 2
-/
lemma ConvergesTo_unique {X : Type} (M : IMetricSpace X) (x : ℕ → X) (X1 X2 : X)
  (hx : ConvergesTo M x X1) (hy : ConvergesTo M x X2) : X1 = X2 := by
  have h_ε : ∀ ε > 0, (M.d X1 X2 < ε) := by
    intro ε hε
    have h1 : ∃ N, ∀ n ≥ N, M.d (x n) X1 < ε / 2 := by
      specialize hx (ε / 3) (by linarith)
      obtain ⟨N, hN⟩ := hx
      use N
      intro n hn
      specialize hN n hn
      linarith
    have h2 : ∃ N, ∀ n ≥ N, M.d (x n) X2 < ε / 2 := by
      specialize hy (ε / 3) (by linarith)
      obtain ⟨N, hN⟩ := hy
      use N
      intro n hn
      specialize hN n hn
      linarith
    obtain ⟨N1, hN1⟩ := h1
    obtain ⟨N2, hN2⟩ := h2
    let N := max N1 N2
    specialize hN1 N (by grind)
    specialize hN2 N (by grind)
    have := M.d_triangle X1 (x N) X2
    rw [M.d_symm] at hN1
    linarith
  have : 0 ≤ M.d X1 X2 := M.d_nonneg X1 X2
  have : M.d X1 X2 = 0 := by
    by_contra hne
    specialize h_ε (M.d X1 X2) (by grind)
    grind
  rwa [M.d_zero_iff_eq X1 X2] at this


structure ConvergentSeq {X : Type} (M : IMetricSpace X) where
  toFun : ℕ → X
  limit : X
  converges : ConvergesTo M toFun limit

structure CauchySeq {X : Type} (M : IMetricSpace X) where
  toFun : ℕ → X
  isCauchy : IsCauchy M toFun

-- A bit shorter in bundled form
lemma ConvergesTo_unique' {X : Type} (M : IMetricSpace X) (x y : ConvergentSeq M) (h : x.toFun = y.toFun) : x.limit = y.limit :=
  ConvergesTo_unique M x.toFun x.limit y.limit x.converges (by grind [y.converges])

@[simps]
def RMetric : IMetricSpace ℝ where
  d := fun x y => |x - y|
  d_nonneg x y := by grind
  d_zero_iff_eq x y := by grind
  d_symm x y := by grind
  d_triangle x y z := by grind

/-
Proposition 4
-/
example {X : Type} (M : IMetricSpace X) (x : ConvergentSeq M) (y : X) : ConvergentSeq RMetric where
  toFun := fun n ↦ M.d (x.toFun n) y
  limit := M.d x.limit y
  converges := by
    intro ε hε
    have h := x.converges
    specialize h ε hε
    obtain ⟨N, hN⟩ := h
    use N
    intro n hn
    simp only [RMetric_d]
    rw [abs_le]
    have hN1 := hN n hn
    have hN2 := hN n hn
    rw [M.d_symm] at hN1
    constructor
    · linarith [M.d_triangle x.limit (x.toFun n) y]
    · linarith [M.d_triangle (x.toFun n) x.limit y]

/-
Proposition 5 - PSET
-/
example {X : Type} (M : IMetricSpace X) (x y : ConvergentSeq M) : ConvergentSeq RMetric where
  toFun := fun n ↦ M.d (x.toFun n) (y.toFun n)
  limit := M.d x.limit y.limit
  converges := by
    sorry

-- I think this requires that ℝ is cauchy-complete
example {X : Type} (M : IMetricSpace X) (x y : CauchySeq M) : ConvergentSeq RMetric where
  toFun := fun n ↦ M.d (x.toFun n) (y.toFun n)
  limit := sorry
  converges := by
    sorry

/-
Definition 6 - Bounded
-/

def IsBoundedSeq {X : Type} (M : IMetricSpace X) (x : ℕ → X) : Prop :=
  ∃ p : X, ∃ B : ℝ, ∀ n, M.d (x n) p ≤ B

structure BoundedSeq {X : Type} (M : IMetricSpace X) where
  toFun : ℕ → X
  isBounded : IsBoundedSeq M toFun

def IsBoundedSubset {X : Type} (M : IMetricSpace X) (A : Set X) : Prop :=
  ∃ p : X, ∃ B : ℝ, ∀ x ∈ A, M.d x p ≤ B

def IsConvergent {X : Type} (M : IMetricSpace X) (x : ℕ → X) : Prop :=
  ∃ l : X, ConvergesTo M x l

/-
Proposition 7 - Every convergent sequence is bounded
-/
example {X : Type} (M : IMetricSpace X) (x : ConvergentSeq M) : BoundedSeq M where
  toFun := x.toFun
  isBounded := by
    obtain ⟨N, hN⟩ := x.converges 1 (by norm_num)
    let B : Finset ℝ := (Finset.range (N + 1)).image (fun n => M.d (x.toFun n) x.limit)
    have h0 : (0 : ℕ) ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.succ_pos N)
    have hB_nonempty : B.Nonempty :=
      ⟨M.d (x.toFun 0) x.limit, Finset.mem_image_of_mem _ h0⟩
    use x.limit, max (B.max' hB_nonempty) 1
    intro n
    by_cases h : n ≤ N
    · refine le_max_of_le_left ?_
      have hmem : M.d (x.toFun n) x.limit ∈ B :=
        Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
      exact Finset.le_max' B _ hmem
    · exact le_max_of_le_right (hN n (by omega))

/-
Proposition 8 - Every convergent sequence is a Cauchy sequence
-/
example {X : Type} (M : IMetricSpace X) (x : ConvergentSeq M) : CauchySeq M where
  toFun := x.toFun
  isCauchy := by
    intro ε hε
    obtain ⟨N, hN⟩ := x.converges (ε / 2) (by linarith)
    use N
    intro n hn m hm
    calc M.d (x.toFun n) (x.toFun m)
      ≤ M.d (x.toFun n) x.limit + M.d x.limit (x.toFun m) := by apply M.d_triangle
    _ ≤ M.d (x.toFun n) x.limit + ε / 2 := by grind [M.d_symm]
    _ ≤ ε / 2 + ε / 2 := by grind
    _ = ε := by ring

/-
Definition 9 - Cauchy complete metric space
-/
def IsCauchyComplete {X : Type} (M : IMetricSpace X) : Prop :=
  ∀ x : ℕ → X, IsCauchy M x → IsConvergent M x

/-
Proposition 11 - Every subsequence of a convergent sequence is convergent to the same limit

TODO: subsequences
-/

/-
Theorem 12 (Properties of open sets)
-/

lemma isOpen_empty {X : Type} (M : IMetricSpace X) : IsOpen M ∅ := by
  intro x hx
  grind

lemma isOpen_univ {X : Type} (M : IMetricSpace X) : IsOpen M Set.univ := by
  intro x _
  use 1
  norm_num

lemma isOpen_sUnion {X : Type} (M : IMetricSpace X) (𝒰 : Set (Set X)) (h : ∀ U ∈ 𝒰, IsOpen M U) : IsOpen M (⋃₀ 𝒰) := by
  sorry

lemma isOpen_inter {X : Type} (M : IMetricSpace X) (A B : Set X) (hA : IsOpen M A) (hB : IsOpen M B) : IsOpen M (A ∩ B) := by
  sorry

/-
Definition 14 - Closed set
-/
def IsClosed {X : Type} (M : IMetricSpace X) (A : Set X) : Prop :=
  IsOpen M (Aᶜ)

/-
Definition 15 - Disconnected and Connected
-/
def IsDisconnected {X : Type} (M : IMetricSpace X) : Prop :=
  ∃ U V : Set X, U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ ∧ IsOpen M U ∧ U ∪ V = Set.univ

def IsConnected {X : Type} (M : IMetricSpace X) : Prop :=
  ¬ IsDisconnected M

/-
Proposition 16
-/

def IsClopen {X : Type} (M : IMetricSpace X) (A : Set X) : Prop :=
  IsClosed M A ∧ IsOpen M A

example {X : Type} (M : IMetricSpace X) (h : IsConnected M)
: ∀ S : Set X, IsClopen M S ↔ S = ∅ ∨ S = Set.univ := by
  sorry

/-
Theorem 18 - properties of closed sets
-/

lemma isClosed_empty {X : Type} (M : IMetricSpace X) : IsClosed M ∅ := by
  simp [IsClosed, isOpen_univ]

lemma isClosed_univ {X : Type} (M : IMetricSpace X) : IsClosed M Set.univ := by
  simp [IsClosed, isOpen_empty]

lemma isClosed_sInter {X : Type} (M : IMetricSpace X) (𝒜 : Set (Set X)) (h : ∀ A ∈ 𝒜, IsClosed M A) : IsClosed M (⋂₀ 𝒜) := by
  sorry

lemma isClosed_union {X : Type} (M : IMetricSpace X) (A B : Set X) (hA : IsClosed M A) (hB : IsClosed M B) : IsClosed M (A ∪ B) := by
  simp [IsClosed]
  sorry

/-
Example 20 - open balls are open
-/

example {X : Type} (M : IMetricSpace X) (x : X) (ε : ℝ) : IsOpen M (Ball M x ε) := by
  sorry

/-
Theorem 21 - an open subset of a metric space is a union of open balls
-/

example {X : Type} (M : IMetricSpace X) (A : Set X) (h : IsOpen M A) : ∃ 𝒰 : Set (Set X), ∀ U ∈ 𝒰, IsOpen M U ∧ A = ⋃₀ 𝒰 := by
  sorry

/-
Example 23 - singleton sets are closed
-/

example {X : Type} (M : IMetricSpace X) (x : X) : IsClosed M {x} := by
  sorry

/-
Remark 24 - finite sets are closed
-/

example {X : Type} (M : IMetricSpace X) (A : Set X) (h : A.Finite) : IsClosed M A := by
  sorry

/-
Proposition 25
-/

example (x : ℕ → ℝ) (x_inf : ℝ)
: ConvergesTo RMetric x x_inf ↔ ∀ ε > 0, { n | x n ∉ Set.Ioo (x_inf - ε) (x_inf + ε) }.Finite := by
  sorry


/-
Definition 26 - Neighborhood
-/

def IsNeighborhood {X : Type} (M : IMetricSpace X) (x : X) (U : Set X) : Prop :=
  x ∈ U ∧ IsOpen M U

/-
Theorem 27
-/

example {X : Type} (M : IMetricSpace X) (x : ℕ → X) (x_inf : X) :
  ConvergesTo M x x_inf ↔ ∀ U, IsNeighborhood M x_inf U → { n | x n ∉ U }.Finite := by
  sorry



/-
Theorem 28
-/

example {X : Type} (M : IMetricSpace X) (x : ℕ → X) (x_inf : X) :
  ConvergesTo M x x_inf ↔ ∀ U, IsNeighborhood M x_inf U → { n | x n ∉ U }.Finite := by
  sorry


end MIT_18_S190
