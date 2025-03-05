import Mathlib
import Mathlib.Tactic
import LeanGT.Texify

set_option linter.unusedTactic false
set_option linter.unusedVariables false

-- Place your cursor next to the `texify` tactic to see the LaTeX code.

-- Algebraic inequalities

theorem motzkin (x y : ℝ) : 0 ≤ x^4 * y^2 + x^2 * y^4  - 3 * x^2 * y^2 + 1 := by
  texify
  intentional_sorry

theorem nesbitt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : (3:ℝ) / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) := by
  texify
  intentional_sorry

theorem imo2008_p2a (x y z : ℝ) (h : x * y * z = 1) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
  -- IMO 2008 P2, from compfiles
    1 ≤ x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 := by
  texify
  intentional_sorry

-- Intervals

example : Finset.Icc 1 3 = Finset.Ico 1 4 := by
  texify
  decide

-- Bigoperators

theorem sum_range_id (n : ℕ) : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := by
  -- Bound variables are shown as ξ₀, ξ₁, etc :(
  texify
  exact Finset.sum_range_id n

theorem imo1966_p4 (n : ℕ) (x : ℝ)
    (hx : ∀ t : ℕ, ∀ k : ℤ, x ≠ k * Real.pi / 2^t) :
    ∑ i ∈ Finset.range n, 1 / Real.sin (2^(i + 1) * x) =
    1 / Real.tan x - 1 / Real.tan (2^n * x) := by
  texify
  intentional_sorry

-- More inequalities

theorem imosl1998SL (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x*y*z = 1)
  : (3:ℝ) / 4 ≤ x^3 / ((1 + y) * (1 + z)) + y^3 / ((1 + z) * (1 + x)) + z^3 / ((1 + x) * (1 + y)):= by
  texify
  intentional_sorry

theorem usamo1998 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : 1 / (a*b*c) ≤ 1 / (a^3 + b^3 + a*b*c) + 1 / (b^3 + c^3 + a*b*c) + 1 / (c^3 + a^3 + a*b*c) := by
  texify
  intentional_sorry

theorem mathlinks (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a*b*c = 1)
: 3 ≤ Real.sqrt ((a + b) / (a + 1)) + Real.sqrt ((b + c) / (b + 1)) + Real.sqrt ((c + a) / (c + 1)) := by
  texify
  intentional_sorry

theorem nesbitt' (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
  : 2 ≤ a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) := by
  texify
  intentional_sorry

theorem example_111 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : a*b + b*c + c*a ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  texify
  intentional_sorry
