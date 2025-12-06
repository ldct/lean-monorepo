import Mathlib

example (a b c : ℝ) : |a + b - c| = |c - a - b| := by
  simp_all only [abs, max_def]
  split_ifs at * <;> linarith

example (a b c : ℝ) (h1 : |a - b| < 1) (h2 : |a - c| < 1) (h3 : 100 < |b - c|) : False := by
  simp_all only [abs, max_def]
  split_ifs at * <;> linarith

example (a b c : ℝ) (h1 : |a - b| < 1) (h2 : |a - c| < 1) (h3 : 100 < |b - c|) : False := by
  simp_all only [abs, max_def]
  split_ifs at * <;> linarith

example (a b c d : ℝ) : 0 < 1 + |a| + |b - (|c - d|)| := by
  simp_all only [abs, max_def]
  split_ifs at * <;> linarith

example (a b : ℝ)
: |(|a|) - (|b|)| ≤ |a - b| := by
  simp_all only [abs, max_def]
  split_ifs at * <;> linarith

example (a b c d : ℝ)
 : (|a + b + c + d| ≤ |a| + |b| + |c| + |d|)
 := by
  simp_all only [abs, max_def]
  split_ifs at * <;> linarith

example (a b c d : ℝ)
: |a| < 1 ↔ 
: (|a + b + c + d| ≤ |a| + |b| + |c| + |d|)
 := by
  simp_all only [abs, max_def]
  split_ifs at * <;> linarith