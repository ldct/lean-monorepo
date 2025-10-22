import Mathlib

/--
https://en.wikipedia.org/wiki/Irregularity_of_distribution
-/
def bucket_property (x : ℕ → ℚ) (N : ℕ) : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → n ≤ N →
  ∀ {k : ℕ}, 1 ≤ k → k ≤ n →
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
      (((k : ℝ) - 1) / (n : ℝ) ≤ x i ∧ x i < (k : ℝ) / (n : ℝ))

def x (n : ℕ) : ℚ := match n with
  | 1 => 0.029
  | 2 => 0.971
  | 3 => 0.423
  | 4 => 0.71
  | 5 => 0.27
  | 6 => 0.524
  | 7 => 0.852
  | 8 => 0.172
  | _ => 0

example : bucket_property x 8 := by
  intro n hn1 hn2 k hk1 hk2
  interval_cases n <;> interval_cases k
  · use 1; simp [x]; norm_num

  · use 1; simp [x]; norm_num
  · use 2; simp [x]; norm_num

  · use 1; simp [x]; norm_num
  · use 3; simp [x]; norm_num
  · use 2; simp [x]; norm_num

  · use 1; simp [x]; norm_num
  · use 3; simp [x]; norm_num
  · use 4; simp [x]; norm_num
  · use 2; simp [x]; norm_num

  · use 1; simp [x]; norm_num
  · use 5; simp [x]; norm_num
  · use 3; simp [x]; norm_num
  · use 4; simp [x]; norm_num
  · use 2; simp [x]; norm_num

  · use 1; simp [x]; norm_num
  · use 5; simp [x]; norm_num
  · use 3; simp [x]; norm_num
  · use 6; simp [x]; norm_num
  · use 4; simp [x]; norm_num
  · use 2; simp [x]; norm_num

  · use 1; simp [x]; norm_num
  · use 5; simp [x]; norm_num
  · use 3; simp [x]; norm_num
  · use 6; simp [x]; norm_num
  · use 4; simp [x]; norm_num
  · use 7; simp [x]; norm_num
  · use 2; simp [x]; norm_num

  · use 1; simp [x]; norm_num
  · use 8; simp [x]; norm_num
  · use 5; simp [x]; norm_num
  · use 3; simp [x]; norm_num
  · use 6; simp [x]; norm_num
  · use 4; simp [x]; norm_num
  · use 7; simp [x]; norm_num
  · use 2; simp [x]; norm_num

  repeat sorry
