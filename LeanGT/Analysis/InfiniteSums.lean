import LeanGT.Analysis.MonotoneConvergence
import Mathlib

-- Infinite sums

def partialSums (b : ℕ → ℝ) : (ℕ → ℝ) :=
  fun n ↦ ∑ i in Finset.range n, b i

def Summable' (b : ℕ → ℝ) : Prop := Converges (partialSums b)

-- The partial sum of a positive sequence is monotone
theorem monotone_psum_of_pos
  {a : ℕ → ℝ}
  (a_pos : ∀ i, 0 ≤ a i)
: Monotone (partialSums a) := by

  -- In a general preorder, proving monotonicity requires checking f(x) ≤ f(y) for all x ≤ y, but since ℕ is discrete, we can just check adjacent pairs x ≤ x+1
  apply monotone_nat_of_le_succ
  intro x
  unfold partialSums

  -- f(x) ≤ f(x+1) becomes ∑ range(x) ai ≤ ∑ range(x+1) ai, and we can rewrite the RHS as ∑ range(x) ai + (x-th term)
  rw [Finset.sum_range_succ_comm]

  -- Simp cancels common terms, leaving just 0 ≤ a x
  simp [a_pos x]
