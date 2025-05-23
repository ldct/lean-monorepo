import LeanGT.Analysis.AlgebraicLimit
import LeanGT.Analysis.InfiniteSums
import LeanGT.Analysis.Bounded
import Mathlib

-- The terms 1/i
def invNats (i : ℕ) : ℝ := (1 / (i+1):ℚ)
-- The nth harmonic number
def s := partialSums invNats

theorem e1 (k : ℕ) : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats i) ≥ (∑ _ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats (2^(k+1)-1)) := by
  gcongr with i hi
  unfold invNats
  simp only [Nat.ofNat_pos, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel,
    one_div, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one]
  gcongr
  norm_cast
  rw [Finset.mem_Ico] at hi
  omega

theorem e2 (k : ℕ) : (∑ _ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats (2^(k+1)-1)) = (1/2) := by
  have : 2^(k + 1) - 2^k = 2^k := by
    rw [pow_succ]
    omega
  unfold invNats
  simp
  rw [this]
  field_simp
  ring

-- Divergence of the harmonic series

theorem s_unbounded_formula (k : ℕ) : s (2^k) ≥ 1 + (k:ℝ)/2 := by
  induction k with
  | zero =>
    simp
    unfold s partialSums invNats
    simp
  | succ k IH =>
    unfold s partialSums
    unfold s partialSums at IH
    rw [congrFun Finset.range_eq_Ico]

    rw [← Finset.sum_Ico_consecutive invNats (by positivity) (show 2^k ≤ 2^(k+1) by gcongr <;> omega)]

    have : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats i) ≥ 1/2 := by
      calc
        (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats i) ≥ (∑ _ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats (2^(k+1)-1)) := e1 k
        _ = 1/2 := e2 k

    have t := calc
      (∑ i ∈ Finset.Ico 0 (2 ^ k), invNats i + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats i) = (∑ i ∈ Finset.range (2 ^ k), invNats i + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats i) := by
        congr
        rw [congrFun Finset.range_eq_Ico]
      (∑ i ∈ Finset.range (2 ^ k), invNats i + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats i) ≥  (1 + k/2) + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), invNats i := by
        gcongr
      _ ≥ 1 + k/2 + 1/2 := by
        gcongr
      _ = 1 + (k+1)/2 := by ring

    push_cast at t
    push_cast
    exact t

theorem s_unbounded : ¬ (Bounded s) := by
  intro s_bdd
  cases' s_bdd with B hB

  have : ∃ k : ℕ, 1 + (k:ℝ)/2 ≥ B := by
    let B' := ⌈B⌉
    have : 0 ≤ B' := Int.le_of_lt (Int.ceil_pos.mpr hB.left)
    lift B' to ℕ using this with B'' hB''
    use 2*B''
    push_cast
    have : (B':ℝ) = B'' := by exact congrArg Int.cast (Eq.symm hB'')
    rw [←this]
    unfold B'
    field_simp
    have : B ≤ ⌈B⌉ := by exact Int.le_ceil B
    linarith

  cases' this with k hk

  have s_2k := s_unbounded_formula k

  have s_2k_bdd := lt_of_abs_lt (hB.right (2^k))
  have s_2k_large : s (2^k) ≥ B := by exact Preorder.le_trans B (1 + ↑k / 2) (s (2 ^ k)) hk s_2k

  linarith

-- Example 2.4.5: The harmonic series diverges
theorem s_diverges : ¬ (Summable' invNats) := by
  intro h
  unfold Summable' at h
  rw [show partialSums invNats = s by rfl] at h
  exact s_unbounded (ConvergesThenBounded h)
