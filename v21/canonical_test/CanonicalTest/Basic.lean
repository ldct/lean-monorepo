import Mathlib
import Canonical

-- prove properties by induction
def add_assoc' (a b c : Nat) : (a + b) + c = a + (b + c) :=
  by canonical

example (a b k : ℝ) (k_pos : k ≠ 0) (eq : k*a = k*b)
: a = b := by
  sorry

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  sorry

example (a b : ℕ) (h1 : a < b) : (2^a < 2^b) := by
  sorry

-- 1/1
theorem ttt
  (k : ℕ) (b : ℕ → ℝ)
: (∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), 1) * b (2 ^ (k + 1))
  = (∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (2 ^ (k + 1))) := by
  simp

-- 0/16
example
  (k : ℕ) (b : ℕ → ℝ)
:  ∑ x ∈ Finset.range (2 ^ (k + 2) - 1), b (x + 1)
  = ∑ x ∈ Finset.range (2 ^ (k + 1) - 1), b (x + 1)
  + ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1)
:= by
  rw [show Finset.range (2 ^ (k + 2) - 1) = Finset.range (2 ^ (k + 1) - 1) ∪ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1) by
    rw [Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico]
    positivity
    gcongr
    norm_num
    norm_num
  ]
  rw [Finset.sum_union]
  rw [Finset.range_eq_Ico]
  exact Finset.Ico_disjoint_Ico_consecutive _ _ _

-- 1/16
example (m : ℕ) : ∃ k : ℕ, m ≤ 2^(k+1) - 1 := by
  sorry
