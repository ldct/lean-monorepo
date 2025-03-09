import LeanGT.Analysis.TendsTo
import Mathlib

-- Infinite sums

-- The sequence 0 → 0, 1 → b₀, 2 → b₀ + b₁, …
def partialSums (b : ℕ → ℝ) : (ℕ → ℝ) :=
  fun n ↦ ∑ i ∈ Finset.range n, b i

def Summable' (b : ℕ → ℝ) : Prop := Converges (partialSums b)

theorem partialSums_succ (b : ℕ → ℝ) (n : ℕ) : partialSums b (n + 1) = partialSums b n + b n := by
  unfold partialSums
  rw [Finset.sum_range_succ_comm]
  rw [add_comm]

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
