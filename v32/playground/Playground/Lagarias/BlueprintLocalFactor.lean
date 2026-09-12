import Playground.Lagarias.EulerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Prime-power logarithmic losses

Blueprint: equations (7.1) and Lemma 7.1. These estimates compare a finite
prime-power logarithm with the logarithm of a geometric divisor factor.
The logarithmic series is Mathlib's proved series, not a numerical expansion.
The tail bound is needed for the least-common-multiple argument in Section 9.
-/

namespace LeanEval.NumberTheory.Lagarias.Blueprint

open Finset

noncomputable def logTerm (q : ℝ) (i : ℕ) : ℝ := q ^ (i + 1) / ((i : ℝ) + 1)
noncomputable def logPartial (q : ℝ) (a : ℕ) : ℝ := ∑ i ∈ range a, logTerm q i
noncomputable def logTail (q : ℝ) (a : ℕ) : ℝ := ∑' i : ℕ, logTerm q (i + a)

lemma logTerm_nonneg {q : ℝ} (hq : 0 ≤ q) (i : ℕ) : 0 ≤ logTerm q i := by
  unfold logTerm
  positivity

lemma hasSum_logTerm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (logTerm q) (-Real.log (1 - q)) :=
  Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg hq0])

lemma logPartial_add_logTail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℕ) :
    logPartial q a + logTail q a = -Real.log (1 - q) := by
  exact ((hasSum_logTerm hq0 hq1).summable.sum_add_tsum_nat_add a).trans
    (hasSum_logTerm hq0 hq1).tsum_eq

lemma logTail_nonneg {q : ℝ} (hq : 0 ≤ q) (a : ℕ) : 0 ≤ logTail q a :=
  tsum_nonneg fun i => logTerm_nonneg hq (i + a)

lemma logPartial_le_neg_log {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℕ) :
    logPartial q a ≤ -Real.log (1 - q) := by
  linarith [logPartial_add_logTail hq0 hq1 a, logTail_nonneg hq0 a]

/-- Bound a logarithmic-series tail by the corresponding geometric tail. -/
lemma logTail_le_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℕ) :
    logTail q a ≤ q ^ (a + 1) / (((a : ℝ) + 1) * (1 - q)) := by
  have hs := (hasSum_logTerm hq0 hq1).summable
  have hsTail : Summable (fun i : ℕ => logTerm q (i + a)) :=
    (summable_nat_add_iff a).mpr hs
  have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (q ^ (a + 1) / ((a : ℝ) + 1))
  calc
    logTail q a ≤ ∑' i : ℕ, (q ^ (a + 1) / ((a : ℝ) + 1)) * q ^ i := by
      apply hsTail.tsum_le_tsum ?_ hgeom.summable
      intro i
      unfold logTerm
      calc
        q ^ (i + a + 1) / ((↑(i + a) : ℝ) + 1) ≤
            q ^ (i + a + 1) / ((a : ℝ) + 1) := by
          apply div_le_div_of_nonneg_left (pow_nonneg hq0 _) (by positivity)
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) i]
        _ = (q ^ (a + 1) / ((a : ℝ) + 1)) * q ^ i := by
          rw [show i + a + 1 = (a + 1) + i by omega, pow_add]
          ring
    _ = (q ^ (a + 1) / ((a : ℝ) + 1)) * (1 - q)⁻¹ := hgeom.tsum_eq
    _ = q ^ (a + 1) / (((a : ℝ) + 1) * (1 - q)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

lemma logTail_le_pow {q : ℝ} (hq0 : 0 ≤ q) (hqhalf : q ≤ 1 / 2) {a : ℕ} (ha : 1 ≤ a) :
    logTail q a ≤ q ^ (a + 1) := by
  have hq1 : q < 1 := by linarith
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hden : 1 ≤ ((a : ℝ) + 1) * (1 - q) := by nlinarith
  exact (logTail_le_geometric hq0 hq1 a).trans (div_le_self (pow_nonneg hq0 _) hden)

lemma self_le_neg_log_one_sub {u : ℝ} (hu : u < 1) : u ≤ -Real.log (1 - u) := by
  have ht := Real.log_le_sub_one_of_pos (sub_pos.mpr hu)
  linarith

/-- A purely analytic enclosure also used in the certificate's error estimates. -/
lemma neg_log_one_sub_le_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    -Real.log (1 - u) ≤ 2 * u := by
  have hpos : 0 < 1 - u := by linarith
  have ht := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at ht
  calc
    -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := ht
    _ = u / (1 - u) := by field_simp <;> ring
    _ ≤ 2 * u := (div_le_iff₀ hpos).mpr (by nlinarith)

/-- `b_p(a)` in the manuscript. -/
noncomputable def primeLogPartial (p : ℝ) (a : ℕ) : ℝ := logPartial p⁻¹ a

/-- `E_p(a)` in the manuscript. -/
noncomputable def primeLogLoss (p : ℝ) (a : ℕ) : ℝ :=
  primeLogPartial p a - Real.log (Robin.eulerFactor p a)

@[simp] lemma primeLogLoss_zero (p : ℝ) : primeLogLoss p 0 = 0 := by
  simp [primeLogLoss, primeLogPartial, logPartial]

lemma primeLogLoss_eq_tail {p : ℝ} (hp : 1 < p) (a : ℕ) :
    primeLogLoss p a = -Real.log (1 - p⁻¹ ^ (a + 1)) - logTail p⁻¹ a := by
  have hq0 : 0 ≤ p⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hp).le
  have hq1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hseries := logPartial_add_logTail hq0 hq1 a
  unfold primeLogLoss primeLogPartial
  rw [Robin.eulerFactor_eq_closed hp,
    Real.log_div (Robin.one_sub_prime_inv_pow_pos hp a).ne' (Robin.one_sub_prime_inv_pos hp).ne']
  linarith

/-- Blueprint Lemma 7.1: every prime-power logarithmic loss is nonnegative. -/
theorem primeLogLoss_nonneg {p : ℝ} (hp : 2 ≤ p) (a : ℕ) : 0 ≤ primeLogLoss p a := by
  rcases a with _ | a
  · simp
  have hp1 : 1 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := inv_nonneg.mpr (by linarith)
  have hqhalf : p⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hu1 : p⁻¹ ^ (a + 1 + 1) < 1 :=
    lt_of_sub_pos (Robin.one_sub_prime_inv_pow_pos hp1 (a + 1))
  rw [primeLogLoss_eq_tail hp1]
  exact sub_nonneg.mpr ((logTail_le_pow hq0 hqhalf (by omega : 1 ≤ a + 1)).trans
    (self_le_neg_log_one_sub hu1))

/-- The omitted positive tail gives the first upper bound of Lemma 7.1. -/
lemma primeLogLoss_le_neg_log {p : ℝ} (hp : 1 < p) (a : ℕ) :
    primeLogLoss p a ≤ -Real.log (1 - p⁻¹ ^ (a + 1)) := by
  rw [primeLogLoss_eq_tail hp]
  exact sub_le_self _ (logTail_nonneg (inv_nonneg.mpr (zero_lt_one.trans hp).le) a)

/-- The quantitative loss bound needed for the LCM sequence (valid even at exponent zero). -/
theorem primeLogLoss_le_two_mul {p : ℝ} (hp : 2 ≤ p) (a : ℕ) :
    primeLogLoss p a ≤ 2 * p⁻¹ ^ (a + 1) := by
  have hp1 : 1 < p := by linarith
  have hq0 : 0 ≤ p⁻¹ := inv_nonneg.mpr (by linarith)
  have hqhalf : p⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hq1 : p⁻¹ ≤ 1 := by linarith
  have hpow : p⁻¹ ^ (a + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hq0).trans (by simpa using hqhalf)
  exact (primeLogLoss_le_neg_log hp1 a).trans
    (neg_log_one_sub_le_two_mul (pow_nonneg hq0 _) hpow)

end LeanEval.NumberTheory.Lagarias.Blueprint
