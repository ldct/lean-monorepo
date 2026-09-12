import Playground.Lagarias.HarmonicBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smoothing calculus for the self-contained blueprint

The functions `g`, `h`, and `w` are exactly (3.6) in the supplied manuscript.
The tangent inequality is the concavity step in Proposition 9.2. We also prove
an explicit version of (2.5), using the previously checked harmonic bound.
No prime-number estimate or Riemann-hypothesis assumption occurs here.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

noncomputable def g (x : ℝ) : ℝ := Real.log (Real.log x)
noncomputable def h (x : ℝ) : ℝ := 1 / (x * Real.log x)
noncomputable def w (x : ℝ) : ℝ := (Real.log x + 1) / (x ^ 2 * (Real.log x) ^ 2)

lemma h_pos {x : ℝ} (hx : 1 < x) : 0 < h x :=
  one_div_pos.mpr (mul_pos (zero_lt_one.trans hx) (Real.log_pos hx))

lemma w_pos {x : ℝ} (hx : 1 < x) : 0 < w x := by
  unfold w
  have hlog := Real.log_pos hx
  have hx0 := zero_lt_one.trans hx
  positivity

lemma hasDerivAt_g {x : ℝ} (hx : 1 < x) : HasDerivAt g (h x) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  convert (Real.hasDerivAt_log hx0).log hl0 using 1 <;>
    dsimp only [g, h] <;> field_simp <;> ring

lemma hasDerivAt_h {x : ℝ} (hx : 1 < x) : HasDerivAt h (-w x) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  convert (hasDerivAt_const x (1 : ℝ)).div
    ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)) (mul_ne_zero hx0 hl0) using 1 <;>
    dsimp only [h, w] <;> field_simp <;> ring

lemma h_strictAntiOn : StrictAntiOn h (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx0 := zero_lt_one.trans hx
  have hlogx := Real.log_pos hx
  have hlogxy := Real.log_lt_log hx0 hxy
  have hprod : x * Real.log x < y * Real.log y :=
    (mul_lt_mul_of_pos_right hxy hlogx).trans
      (mul_lt_mul_of_pos_left hlogxy (zero_lt_one.trans hy))
  exact one_div_lt_one_div_of_lt (mul_pos hx0 hlogx) hprod

/-- The elementary supporting-line inequality for the natural logarithm. -/
lemma log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y - x) / x := by
  have ht := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at ht
  have heq : y / x - 1 = (y - x) / x := by field_simp; ring
  rw [heq] at ht
  linarith

/-- Concavity in the exact form used at `y = psi x` in Proposition 9.2. -/
lemma g_le_tangent {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    g y ≤ g x + h x * (y - x) := by
  have hx0 := zero_lt_one.trans hx
  have hlogx := Real.log_pos hx
  have hfirst := log_le_tangent hx0 (zero_lt_one.trans hy)
  have hsecond := log_le_tangent hlogx (Real.log_pos hy)
  unfold g h
  calc
    Real.log (Real.log y) ≤ Real.log (Real.log x) +
        (Real.log y - Real.log x) / Real.log x := hsecond
    _ ≤ Real.log (Real.log x) + ((y - x) / x) / Real.log x := by
      apply add_le_add_left
      exact div_le_div_of_nonneg_right (by linarith only [hfirst]) hlogx.le
    _ = Real.log (Real.log x) + 1 / (x * Real.log x) * (y - x) := by
      field_simp
      ring

lemma rhs_pos {n : ℕ} (hn : 0 < n) : 0 < rhs n := by
  have ht := rhs_mono (by norm_num : 0 < (1 : ℕ)) (show 1 ≤ n by omega)
  rw [rhs_one] at ht
  linarith

/-- An explicit replacement for the big-O statement (2.5) in the blueprint. -/
theorem log_rhs_div_le {n : ℕ} (hn : 3 ≤ n) :
    Real.log (rhs n / (n : ℝ)) ≤ Real.eulerMascheroniConstant + g (Real.log (n : ℝ)) +
      16 / (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))) := by
  let L : ℝ := Real.log (n : ℝ)
  let T : ℝ := Real.log L
  let A : ℝ := Real.exp Real.eulerMascheroniConstant * T
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL1 : 1 < L := one_lt_log hn
  have hL0 : 0 < L := zero_lt_one.trans hL1
  have hT0 : 0 < T := Real.log_pos hL1
  have hA0 : 0 < A := mul_pos (Real.exp_pos _) hT0
  have hEA : 1 ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.one_le_exp_iff.mpr gamma_pos.le
  have hTA : T ≤ A := by dsimp [A]; nlinarith
  have hupper := div_le_div_of_nonneg_right (rhs_le_robinBound_add_sixteen hn) hnR.le
  have hrewrite : (robinBound n + 16 * (n : ℝ) / L) / (n : ℝ) = A + 16 / L := by
    dsimp [robinBound, A, T, L]
    field_simp
    ring
  change rhs n / (n : ℝ) ≤ (robinBound n + 16 * (n : ℝ) / L) / (n : ℝ) at hupper
  rw [hrewrite] at hupper
  have hlog := log_le_tangent hA0 (div_pos (rhs_pos hn0) hnR)
  have hlogA : Real.log A = Real.eulerMascheroniConstant + g L := by
    dsimp [A, T, g]
    rw [Real.log_mul (Real.exp_ne_zero _) hT0.ne', Real.log_exp]
  change Real.log (rhs n / (n : ℝ)) ≤ Real.eulerMascheroniConstant + g L + 16 / (L * T)
  calc
    Real.log (rhs n / (n : ℝ)) ≤ Real.log A + (rhs n / (n : ℝ) - A) / A := hlog
    _ ≤ Real.log A + (16 / L) / A := by
      apply add_le_add_left
      exact div_le_div_of_nonneg_right (by linarith only [hupper]) hA0.le
    _ ≤ Real.log A + (16 / L) / T := by
      gcongr
    _ = Real.eulerMascheroniConstant + g L + 16 / (L * T) := by rw [hlogA, div_div]

end LeanEval.NumberTheory.Lagarias.Blueprint
