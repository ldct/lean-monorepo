import Mathlib

attribute [grind =] abs_eq_abs
attribute [grind =] lt_abs
attribute [grind =] abs_lt

attribute [grind] max_comm
attribute [grind] max_self
attribute [grind] max_assoc

@[grind =]
theorem abs_eq_max (a : ℝ) : |a| = max a (-a) := by rfl

example (a b : ℝ) : max a b = max b a := by grind
example (a : ℝ) : max a a = a := by grind
example (a b c : ℝ) : max a (max b c) = max (max c a) b := by grind
example (a : ℝ) : |a| = max a (-a) := by grind
example (a : ℝ) : max a (-a) = max (-a) a := by grind
example (a : ℝ) : a = - (-a) := by grind
example (a : ℝ) : |a| = |-a| := by grind

example (a b c : ℝ) : |a + b - c| = |c - a - b| := by grind
example (a b c : ℝ) (h1 : |a - b| < 1) (h2 : |a - c| < 1) (h3 : 100 < |b - c|) : False := by grind


theorem abs_lt' (a b : ℝ) : |a| < b ↔ a < b ∧ -a < b := by
  grind

macro "absarith" : tactic => `(tactic|
  (try repeat rw [abs_lt'] at *;
   try repeat rw [lt_div_iff₀ (by assumption)] at *;
   constructor <;>
   nlinarith (config := {splitHypotheses := true})))

variable (f : ℝ → ℝ) (t c ε y : ℝ) (hc : 0 < c) (hε : 0 < ε) in
example (h : |f y - f t| < ε / c) :
    |c * f y - c * f t| < ε := by
  absarith
