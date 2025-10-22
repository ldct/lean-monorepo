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

variable (f : ℝ → ℝ) (t c ε y : ℝ) (hc : 0 < c) (hε : 0 < ε)

theorem abs_lt' (a b : ℝ) : |a| < b ↔ a < b ∧ -a < b := by
  grind

macro "absarith" : tactic => `(tactic|
  (try repeat rw [abs_lt'] at *;
   try repeat rw [lt_div_iff₀ (by assumption)] at *;
   constructor <;>
   nlinarith (config := {splitHypotheses := true})))

example (h : |f y - f t| < ε / c) :
    |c * f y - c * f t| < ε := by
  absarith

@[grind ext]
structure RealIsometry where
  f : ℝ → ℝ
  is_isometry : ∀ x y, |f x - f y| = |x - y|

def RealIsometry.identity : RealIsometry where
  f := id
  is_isometry := by grind

def reflection (c : ℝ) : RealIsometry where
  f x := 2 * c - x
  is_isometry x y := by grind

def translation (d : ℝ) : RealIsometry where
  f x := x + d
  is_isometry x y := by grind

def RealIsometry.comp (a : RealIsometry) (b : RealIsometry) : RealIsometry where
  f := a.f ∘ b.f
  is_isometry x y := by grind

instance : One RealIsometry where
  one := RealIsometry.identity

instance : Mul RealIsometry where
  mul a b := RealIsometry.comp a b

instance : Monoid RealIsometry where
  mul a b := RealIsometry.comp a b
  mul_assoc a b c := by rfl
  one_mul a := by rfl
  mul_one a := by rfl

example : (1 : RealIsometry) * (1 : RealIsometry) = 1 := rfl
