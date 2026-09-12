import Playground.Lagarias.HarmonicBounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Exact finite certificates for the Lagarias inequality

The certificate generator is untrusted. Soundness is proved here, and every
certificate is checked by Lean's ordinary kernel reduction, not `native_decide`.

A certificate for an interval `[a,b]` supplies an integer upper bound for the
sum of divisors throughout the interval. A rational lower bound for `H_a`, a
Taylor lower bound for its exponential, and a power-based lower bound for its
logarithm then establish the Lagarias inequality on the whole interval.
-/

namespace LeanEval.NumberTheory.Lagarias.FiniteCertificates

open scoped ArithmeticFunction.sigma

/-- A common-denominator lower approximation to the harmonic number. -/
def harmonicFloor (q n : ℕ) : ℕ := ∑ i ∈ Finset.range n, q / (i + 1)

lemma harmonicFloor_le (q n : ℕ) (hq : 0 < q) :
    (harmonicFloor q n : ℚ) / (q : ℚ) ≤ harmonic n := by
  unfold harmonicFloor harmonic
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  rw [← one_div]
  apply (div_le_div_iff₀ (by exact_mod_cast hq : (0 : ℚ) < q)
    (by positivity : (0 : ℚ) < (i + 1 : ℕ))).2
  simp only [one_mul]
  exact_mod_cast Nat.div_mul_le_self q (i + 1)

/-- Truncating the exponential series gives a rational lower bound. -/
def expLower (h : ℚ) (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k, h ^ i / (i.factorial : ℚ)

lemma expLower_le (h : ℚ) (k : ℕ) (hh : 0 ≤ h) :
    (expLower h k : ℝ) ≤ Real.exp (h : ℝ) := by
  unfold expLower
  push_cast
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hh) k

/-- The logarithm estimate uses only `log x <= x - 1`, applied to an inverse. -/
lemma log_lower_of_power {b h : ℚ} (m : ℕ) (hb : 0 < b) (hpow : b ^ m ≤ h) :
    (((m : ℚ) * (1 - 1 / b) : ℚ) : ℝ) ≤ Real.log (h : ℝ) := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hbR)
  rw [Real.log_inv] at h
  have hbase : 1 - 1 / (b : ℝ) ≤ Real.log (b : ℝ) := by
    simp only [one_div]
    linarith
  push_cast
  calc
    (m : ℝ) * (1 - 1 / (b : ℝ)) ≤ (m : ℝ) * Real.log (b : ℝ) :=
      mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg m)
    _ = Real.log ((b : ℝ) ^ m) := (Real.log_pow (b : ℝ) m).symm
    _ ≤ Real.log (h : ℝ) :=
      Real.log_le_log (pow_pos hbR m) (by exact_mod_cast hpow)

lemma rationalCertificate_sound {n k m : ℕ} {h b : ℚ}
    (hH : h ≤ harmonic n) (hh : 0 < h) (hb : 0 < b) (hpow : b ^ m ≤ h)
    (hl : 0 ≤ (m : ℚ) * (1 - 1 / b)) :
    ((h + expLower h k * ((m : ℚ) * (1 - 1 / b)) : ℚ) : ℝ) ≤ bound n := by
  have hHR : (h : ℝ) ≤ (harmonic n : ℝ) := by exact_mod_cast hH
  have he : (expLower h k : ℝ) ≤ Real.exp (harmonic n : ℝ) :=
    (expLower_le h k hh.le).trans (Real.exp_le_exp.mpr hHR)
  have hlog : (((m : ℚ) * (1 - 1 / b) : ℚ) : ℝ) ≤
      Real.log (harmonic n : ℝ) :=
    (log_lower_of_power m hb hpow).trans
      (Real.log_le_log (by exact_mod_cast hh) hHR)
  have hp := mul_le_mul he hlog (by exact_mod_cast hl) (Real.exp_pos _).le
  simpa only [bound, Rat.cast_add, Rat.cast_mul] using add_le_add hHR hp

lemma bound_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : bound a ≤ bound b := by
  have hH := harmonic_monotone_real hab
  have haH : 0 < (harmonic a : ℝ) :=
    zero_lt_one.trans_le (one_le_harmonic_real ha)
  exact add_le_add hH (mul_le_mul (Real.exp_le_exp.mpr hH)
    (Real.log_le_log haH hH) (Real.log_nonneg (one_le_harmonic_real ha))
    (Real.exp_pos _).le)

/-- A computable divisor sum using the already-proved prime-factor formula. -/
def fastSigma (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i

lemma sigma_eq_fastSigma {n : ℕ} (hn : n ≠ 0) : σ 1 n = fastSigma n := by
  simpa [fastSigma] using
    (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hn)

structure Block where
  lo : ℕ
  hi : ℕ
  upper : ℕ
  logBaseNumerator : ℕ
  deriving DecidableEq, Repr

def harmonicLower (n : ℕ) : ℚ := (harmonicFloor 1000000 n : ℚ) / 1000000

def logBase (c : Block) : ℚ := (c.logBaseNumerator : ℚ) / 100000

def logLower (c : Block) : ℚ := 64 * (1 - 1 / logBase c)

/-- All numerical obligations are rational or natural-number comparisons. -/
def Valid (c : Block) : Prop :=
  0 < c.lo ∧ c.lo ≤ c.hi ∧
  0 < harmonicLower c.lo ∧ 0 < logBase c ∧
  logBase c ^ 64 ≤ harmonicLower c.lo ∧
  0 ≤ logLower c ∧
  (c.upper : ℚ) ≤ harmonicLower c.lo + expLower (harmonicLower c.lo) 30 * logLower c ∧
  ∀ n ∈ Finset.Icc c.lo c.hi, fastSigma n ≤ c.upper

instance (c : Block) : Decidable (Valid c) := by
  unfold Valid
  infer_instance

lemma Valid.sound {c : Block} (hc : Valid c) {n : ℕ}
    (hlo : c.lo ≤ n) (hhi : n ≤ c.hi) : ((σ 1 n : ℕ) : ℝ) ≤ bound n := by
  rcases hc with ⟨hc0, hcle, hh, hb, hpow, hl, hupper, hs⟩
  have hH : harmonicLower c.lo ≤ harmonic c.lo :=
    harmonicFloor_le 1000000 c.lo (by norm_num)
  have hcert := rationalCertificate_sound (k := 30) (m := 64) hH hh hb hpow hl
  have hsmall : (c.upper : ℝ) ≤ bound c.lo :=
    (by exact_mod_cast hupper : (c.upper : ℝ) ≤
      ((harmonicLower c.lo + expLower (harmonicLower c.lo) 30 * logLower c : ℚ) : ℝ)).trans
        hcert
  have hsigma : σ 1 n ≤ c.upper := by
    rw [sigma_eq_fastSigma (by omega)]
    exact hs n (Finset.mem_Icc.mpr ⟨hlo, hhi⟩)
  exact (by exact_mod_cast hsigma : ((σ 1 n : ℕ) : ℝ) ≤ (c.upper : ℝ)).trans
    (hsmall.trans (bound_mono hc0 hlo))

/-- Verify valid interval certificates with no gaps, including coverage of the endpoint. -/
def verifyBlocks (lo hi : ℕ) : List Block → Bool
  | [] => decide (hi < lo)
  | c :: cs => decide (c.lo = lo ∧ Valid c) && verifyBlocks (c.hi + 1) hi cs

lemma verifyBlocks_sound (cs : List Block) (lo hi : ℕ)
    (hv : verifyBlocks lo hi cs = true) :
    ∀ n, lo ≤ n → n ≤ hi → ((σ 1 n : ℕ) : ℝ) ≤ bound n := by
  induction cs generalizing lo with
  | nil =>
      simp only [verifyBlocks, decide_eq_true_eq] at hv
      intro n hn hn'
      omega
  | cons c cs ih =>
      simp only [verifyBlocks, Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases hv with ⟨⟨hlo, hc⟩, hrest⟩
      intro n hn hn'
      by_cases h : n ≤ c.hi
      · exact hc.sound (by omega) h
      · exact ih (c.hi + 1) hrest n (by omega) hn'

end LeanEval.NumberTheory.Lagarias.FiniteCertificates
