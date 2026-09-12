import Playground.Lagarias.BlueprintLCM
import Playground.Lagarias.BlueprintSmoothing

/-!
# The arithmetic half of the converse

Blueprint: Proposition 9.2. We obtain the explicit choice `C = 134`, `a* = 32`
for its unspecified constants. A weaker elementary Chebyshev estimate
`x/8 <= psi x` suffices, so no prime number theorem or asymptotic estimate is
assumed. The function `J` is exactly the finite expression (3.7), with `B`
grouped by prime as in `BlueprintLCM`.

The improper-integral representation of `J`, its limit at infinity, and the
Mellin argument forcing RH are not asserted by this file.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open scoped ArithmeticFunction.sigma

noncomputable def R (x : ℝ) : ℝ := Chebyshev.psi x - x

/-- The finite expression defining the smoothed error in (3.7). -/
noncomputable def J (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + g x + h x * R x - B x

lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have ht := log_le_tangent (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1)
  norm_num at ht
  linarith

lemma log_le_quarter_add_two {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 4 + 2 := by
  have hnorm := Real.log_le_sub_one_of_pos (div_pos ht (by norm_num : (0 : ℝ) < 4))
  rw [Real.log_div ht.ne' (by norm_num)] at hnorm
  have hfour := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith

/-- A deliberately coarse Chebyshev lower bound adequate for Proposition 9.2. -/
lemma psi_ge_eighth {x : ℝ} (hx : 20 ≤ x) : x / 8 ≤ Chebyshev.psi x := by
  let n : ℕ := ⌊x⌋₊
  have hfloor : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog := log_le_quarter_add_two (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have hpsi := Chebyshev.psi_ge n
  have hsame : Chebyshev.psi (n : ℝ) = Chebyshev.psi x :=
    (Chebyshev.psi_eq_psi_coe_floor x).symm
  rw [hsame] at hpsi
  have hmain : (n : ℝ) / 2 ≤ (n : ℝ) * Real.log 2 := by
    nlinarith [half_le_log_two]
  linarith

lemma three_le_lcmSeq {x : ℝ} (hx : 32 ≤ x) : 3 ≤ lcmSeq x := by
  have hpsi : 4 ≤ Chebyshev.psi x := by
    linarith [psi_ge_eighth (by linarith : 20 ≤ x)]
  have hLpos : (0 : ℝ) < lcmSeq x := by exact_mod_cast lcmSeq_pos x
  by_contra hnot
  have hLle : lcmSeq x ≤ 2 := by omega
  have hLleR : (lcmSeq x : ℝ) ≤ 2 := by exact_mod_cast hLle
  have hlog := Real.log_le_sub_one_of_pos hLpos
  rw [log_lcmSeq] at hlog
  linarith

lemma harmonic_error_at_psi_le {x : ℝ} (hx : 32 ≤ x) :
    16 / (Chebyshev.psi x * Real.log (Chebyshev.psi x)) ≤ 128 / Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hpsilower := psi_ge_eighth (by linarith : 20 ≤ x)
  have hpsi4 : 4 ≤ Chebyshev.psi x := by linarith
  have hpsi0 : 0 < Chebyshev.psi x := by linarith
  have hlog3 : 1 < Real.log (3 : ℝ) := by
    simpa using one_lt_log (by norm_num : 3 ≤ (3 : ℕ))
  have hlogpsi : 1 ≤ Real.log (Chebyshev.psi x) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have hden : x / 8 ≤ Chebyshev.psi x * Real.log (Chebyshev.psi x) := by
    nlinarith
  have hs0 : 0 < Real.sqrt x := by linarith [sqrt_ge_two (by linarith : 4 ≤ x)]
  have hsle : Real.sqrt x ≤ x := by
    have hs2 := sqrt_ge_two (by linarith : 4 ≤ x)
    nlinarith [Real.sq_sqrt hx0.le]
  calc
    16 / (Chebyshev.psi x * Real.log (Chebyshev.psi x)) ≤ 16 / (x / 8) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 128 / x := by ring
    _ ≤ 128 / Real.sqrt x := div_le_div_of_nonneg_left (by norm_num) hs0 hsle

/-- Proposition 9.2 with explicit constants, derived from the pointwise criterion.
No RH, Mertens theorem, or oscillation hypothesis is a theorem argument. -/
theorem J_lower_of_lagarias
    (hcriterion : ∀ n : ℕ, 1 ≤ n → ((σ 1 n : ℕ) : ℝ) ≤ rhs n)
    {x : ℝ} (hx : 32 ≤ x) : -(134 / Real.sqrt x) ≤ J x := by
  have hL3 := three_le_lcmSeq hx
  have hLpos : (0 : ℝ) < lcmSeq x := by exact_mod_cast lcmSeq_pos x
  have hSigma : (0 : ℝ) < ((σ 1 (lcmSeq x) : ℕ) : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 (lcmSeq x) (Nat.ne_of_gt (lcmSeq_pos x))
  have hcompare :
      Real.log (((σ 1 (lcmSeq x) : ℕ) : ℝ) / (lcmSeq x : ℝ)) ≤
        Real.log (rhs (lcmSeq x) / (lcmSeq x : ℝ)) :=
    Real.log_le_log (div_pos hSigma hLpos)
      (div_le_div_of_nonneg_right (hcriterion (lcmSeq x) (by omega)) hLpos.le)
  have hupper := log_rhs_div_le hL3
  rw [log_lcmSeq] at hupper
  have hpsi1 : 1 < Chebyshev.psi x := by
    linarith [psi_ge_eighth (by linarith : 20 ≤ x)]
  have htangent := g_le_tangent (by linarith : 1 < x) hpsi1
  have hlower := log_sigma_lcmSeq_ge (by linarith : 4 ≤ x)
  have herror := harmonic_error_at_psi_le hx
  unfold J R
  have hcombine : -(6 / Real.sqrt x + 128 / Real.sqrt x) ≤
      Real.eulerMascheroniConstant + g x + h x * (Chebyshev.psi x - x) - B x := by
    linarith
  convert hcombine using 1 <;> ring

end LeanEval.NumberTheory.Lagarias.Blueprint
