import Mathlib

attribute [grind =] abs_eq_abs
attribute [grind =] lt_abs
attribute [grind =] abs_lt

example (a b c : ℝ) : |a + b - c| = |c - a - b| := by grind
example (a b c : ℝ) (h1 : |a - b| < 1) (h2 : |a - c| < 1) (h3 : 100 < |b - c|) : False := by grind

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
