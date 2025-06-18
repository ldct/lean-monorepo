import LeanGT.Analysis.MonotoneConvergence
import LeanGT.Analysis.InfiniteSums
import Mathlib

-- This file proves that the series ∑ 1/n^2 converges to some limit
-- The bulk of this is a series of inequalities that show that the partial sums are bounded above by 2

noncomputable def invSquares (i : ℕ) : ℝ := (1 / ((i+1)^2))
noncomputable def bassel := partialSums invSquares

-- first inequality
theorem bb1 (m : ℕ) : bassel m ≤ ∑ i ∈ Finset.range m, if i = 0 then 1 else (1/((i:ℝ)+1) * (1/i)) := by
  -- Unfold everything to ∑ and do a term-by-term comparison
  unfold bassel partialSums invSquares
  gcongr with i hi

  cases ne_or_eq i 0

  case h.inl i_ne_0 =>
    simp only [i_ne_0, reduceIte]
    rw [← (one_div_pow ((i:ℝ) + 1) 2)]
    rw [show (1 / ((i:ℝ) + 1))^2 = (1 / ((i:ℝ) + 1)) * (1 / ((i:ℝ) + 1)) by ring]
    gcongr
    norm_num

  case h.inr i_eq_0 =>
    simp [i_eq_0]

theorem bb2 (m : ℕ) : (∑ i ∈ Finset.range m, if i = 0 then 1 else (1/((i:ℝ)+1) * (1/i))) = ∑ i ∈ Finset.range m, if i = 0 then 1 else ((1/i:ℝ) - 1/(i+1)) := by
  congr
  funext i

  cases ne_or_eq i 0
  case h.inl i_ne_0 =>
    simp [i_ne_0]
    field_simp
    ring

  case h.inr i_eq_0 =>
    simp [i_eq_0]

theorem bb3 (m : ℕ) (hm : 1 ≤ m) : (∑ i ∈ Finset.range m, if i = 0 then 1 else ((1/i:ℝ) - 1/(i+1))) = 2 - 1/(m:ℝ) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show Finset.range 1 = {0} by decide]
    simp
    norm_num
  | succ n t IH =>
    rw [Finset.sum_range_succ_comm]
    simp only [show n ≠ 0 by positivity, reduceIte]
    rw [IH]
    push_cast
    ring_nf

theorem final (m : ℕ) : bassel m ≤ 2 := by
  cases Nat.le_total 1 m

  case inl hm => calc
    bassel m ≤ ∑ i ∈ Finset.range m, if i = 0 then 1 else (1/((i:ℝ)+1) * (1/i)) := bb1 m
    _ = ∑ i ∈ Finset.range m, if i = 0 then 1 else ((1/i:ℝ) - 1/(i+1)) := bb2 m
    _ = 2 - 1/(m:ℝ) := bb3 m hm
    _ ≤ 2 := by
      have : 0 < 1/(m:ℝ) := by positivity
      linarith

  case inr hm =>
    have : m = 0 ∨ m = 1 := by exact Nat.le_one_iff_eq_zero_or_eq_one.mp hm

    cases this

    case inl m_eq_0 =>
      rw [m_eq_0]
      unfold bassel partialSums
      simp

    case inr m_eq_1 =>
      rw [m_eq_1]
      unfold bassel partialSums invSquares
      simp

-- Example 2.4.4: ∑ 1/n^2 converges to some (presently unknown) limit
theorem c1 : Summable' invSquares := by
  rw [Summable']

  refine MCT ?monotone ?bounded

  case monotone =>
    apply monotone_psum_of_pos
    intro i
    unfold invSquares
    positivity

  case bounded =>
    use 2
    intro n
    exact final n
