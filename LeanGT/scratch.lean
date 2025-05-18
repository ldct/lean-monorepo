import Mathlib
import LeanTeXMathlib

-- example
-- (m : ℕ)
-- (M p: ℝ)
-- (hm : M < m)
-- (M_bounds : abs (∑ x ∈ Finset.range m, (2 ^ x) ^ (1 - p)) < M)
-- : False := by
--   rw [abs_of_nonneg (by positivity)] at M_bounds
--   sorry

-- theorem pd_false (a : ℕ → ℝ) : partialSums (drop a) = drop (partialSums a) := by
--   sorry -- false theorem

example
  (a b: ℝ)
  (ha : 0 ≠ a)
: 1 / b = a / (a * b) := by
  have : b = 0 ∨ b ≠ 0 := by exact eq_or_ne b 0
  cases' this with h1 h2
  rw [h1]
  simp
  field_simp

example
  (j : ℕ)
  (sylvester : ℕ → ℕ)
  (test : 2 ≤ sylvester j)
: 0 ≠ (sylvester j) - (1:ℚ) := by
  qify at test
  linarith
  omega

example
  (a b: ℝ)
  (ha : 0 ≠ a)
  -- (hb : 0 ≠ b)
: 1 / b = a / (a * b) := by
  field_simp

example
  (a b : ℝ)
  (h1 : a^2 ≤ 2)
  (h2 : b^2 ≤ 3)
: abs (a^2 + b^2) ≤ 5 := by
  rw [abs_of_nonneg (by positivity)]
  linarith

open LeanTeX
macro "latex_pp_well_known_func_rule" c:ident tex:str : command =>
  `(
  latex_pp_app_rules (const := $c)
    | _, #[x] => do
      let v ← latexPP x
      return LatexData.atomString $tex ++ " " ++ v.protect (funAppBP - 1)
        |>.mergeBP (lbp := .NonAssoc funAppBP) (rbp := .NonAssoc funAppBP)
  )

latex_pp_well_known_func_rule Real.exp "\\exp"
latex_pp_well_known_func_rule Real.log "\\log"

example (x y : ℝ )
  (hp : (x+y)^2 > 0)
  (h' : 4 * x * y ≤ (x + y) ^ 2) :
    x*y/(x+y)^2 ≤ 1 / 4 := by {
  -- h' is almost the goal, mathematically just need to
  -- "multiply both sides of the goal by 4 * (x + y) ^ 2, its fine because hp"
  have hpp : 4 * (x + y) ^ 2 > 0 := by positivity
  apply_fun OrderIso.mulRight₀ (4 * (x + y) ^ 2) hpp
  simp
  move_mul [← 4]
  field_simp
  rw [← mul_assoc]
  convert h'
}

example
  (a b : ℝ)
  (ha : a ≠ 0)
: 1 = a/b := by
  field_simp
  exact?
