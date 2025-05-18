import LeanGT.Analysis.AlgebraicLimit
import LeanGT.Analysis.InfiniteSums
import Mathlib

-- Define `drop` and `pad`, reindexing sequences from different points.

def drop (a : ℕ → ℝ) : ℕ → ℝ := fun i ↦ a (i + 1)

def pad (a : ℕ → ℝ) : ℕ → ℝ := fun i ↦ a (i - 1)

theorem tdrop (a : ℕ → ℝ) (l : ℝ): TendsTo a l ↔ TendsTo (drop a) l := by
  constructor
  case mp =>
    intro h
    unfold TendsTo at *
    intro ε ε_pos
    specialize h ε ε_pos
    cases' h with B hB
    use B
    intro n hn
    specialize hB (n+1)
    unfold drop
    exact hB (by omega)
  case mpr =>
    intro h
    unfold TendsTo at *
    intro ε ε_pos
    specialize h ε ε_pos
    cases' h with B hB
    use B+1
    intro n hn
    have : 0 < n := by omega
    specialize hB (n-1)
    unfold drop at hB
    rw [show n - 1 + 1 = n by omega] at hB
    exact hB (by omega)

theorem cdrop (a : ℕ → ℝ): Converges a ↔ Converges (drop a) := by
  unfold Converges
  constructor
  case mp =>
    intro h
    cases' h with l hl
    rw [tdrop] at hl
    use l
  case mpr =>
    intro h
    cases' h with l hl
    rw [←tdrop] at hl
    exact Exists.intro l hl


theorem ri
(i : ℕ)
(a : ℕ → ℝ)
: ∑ x ∈ Finset.range i, a (x + 1) = ∑ x ∈ Finset.Ico 1 (i + 1), a x := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add']
  -- can also do apply Finset.sum_bij (fun x _ ↦ x + 1)

theorem pd (a : ℕ → ℝ) :
drop (partialSums a) = fun i ↦ (partialSums (drop a) i) + a 0 := by
  ext i
  unfold drop partialSums
  simp
  rw [ri]
  rw [add_comm _ (a 0)]
  exact Finset.sum_range_eq_add_Ico a (by omega) -- simproc?

theorem pd' (a : ℕ → ℝ) :
partialSums (drop a) = fun i ↦ (drop (partialSums a) i) - a 0 := by
  ext i
  rw [pd]
  simp

theorem conv_sum_const
  (a : ℕ → ℝ)
  (k : ℝ)
: Converges a ↔ Converges (fun i ↦ (a i + k)) := by sorry

theorem conv_drop (a : ℕ → ℝ) : Summable' a ↔ Summable' (drop a) := by
  constructor
  case mp =>
    unfold Summable' Converges
    intro h
    cases' h with l h
    use l - (a 0)
    rw [pd']
    apply tendsTo_sum
    rw [← tdrop]
    exact h
    intro ε hε
    use 1
    intro n hn
    simp
    exact hε
  case mpr =>
    intro h
    unfold Summable' at *
    rw [pd'] at h
    have h : Converges fun i ↦ drop (partialSums a) i - a 0 + a 0 := by exact (conv_sum_const (fun i ↦ drop (partialSums a) i - a 0) (a 0)).mp h
    simp at h
    rw [show (fun i ↦ (drop (partialSums a) i)) = drop (partialSums a) by rfl] at h
    exact (cdrop (partialSums a)).mpr h


theorem conv_pad (a : ℕ → ℝ) : Summable' a ↔ Summable' (pad a) := by
  sorry
