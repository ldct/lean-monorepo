import Playground.Lagarias.PrimePower

/-!
# Parameter thresholds for colossally abundant numbers

`primeThreshold p k` is the classical function `F(p,k+1)`: the exponent index
starts at zero to match an increase from `p^k` to `p^(k+1)`. The inequalities
here keep equality cases and therefore do not assume unique maximizers.

The existence argument is elementary: the geometric sum is at least `k+1`,
so its reciprocal eventually becomes smaller than `p^epsilon - 1`.
-/

namespace LeanEval.NumberTheory.Lagarias.Robin

open Finset

/-- The critical parameter for the adjacent exponents `k` and `k+1`.
This is `F(p,k+1)` in the cited literature. -/
noncomputable def primeThreshold (p : ℝ) (k : ℕ) : ℝ :=
  Real.log (primeIncrement p k) / Real.log p

@[simp] lemma primeThreshold_zero (p : ℝ) :
    primeThreshold p 0 = Real.log (1 + 1 / p) / Real.log p := by
  simp [primeThreshold]

lemma primeThreshold_pos {p : ℝ} (hp : 1 < p) (k : ℕ) :
    0 < primeThreshold p k := by
  exact div_pos (Real.log_pos (one_lt_primeIncrement (zero_lt_one.trans hp) k))
    (Real.log_pos hp)

lemma primeThreshold_strictAnti {p : ℝ} (hp : 1 < p) : StrictAnti (primeThreshold p) := by
  intro a b hab
  apply div_lt_div_of_pos_right ?_ (Real.log_pos hp)
  exact Real.log_lt_log (primeIncrement_pos (zero_lt_one.trans hp) b)
    (primeIncrement_strictAnti (zero_lt_one.trans hp) hab)

lemma primeIncrement_le_rpow_iff {p : ℝ} (hp : 1 < p) (ε : ℝ) (k : ℕ) :
    primeIncrement p k ≤ p ^ ε ↔ primeThreshold p k ≤ ε := by
  have hp0 := zero_lt_one.trans hp
  unfold primeThreshold
  rw [div_le_iff₀ (Real.log_pos hp), ← Real.log_rpow hp0]
  exact (Real.log_le_log_iff (primeIncrement_pos hp0 k) (Real.rpow_pos_of_pos hp0 ε)).symm

lemma rpow_le_primeIncrement_iff {p : ℝ} (hp : 1 < p) (ε : ℝ) (k : ℕ) :
    p ^ ε ≤ primeIncrement p k ↔ ε ≤ primeThreshold p k := by
  have hp0 := zero_lt_one.trans hp
  unfold primeThreshold
  rw [le_div_iff₀ (Real.log_pos hp), ← Real.log_rpow hp0]
  exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hp0 ε) (primeIncrement_pos hp0 k)).symm

lemma primeSum_mono_base {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (k : ℕ) :
    primeSum p k ≤ primeSum q k := by
  unfold primeSum
  gcongr

lemma primeIncrement_lt_of_lt_base {p q : ℝ} (hp : 0 < p) (hpq : p < q) (k : ℕ) :
    primeIncrement q k < primeIncrement p k := by
  have hq : 0 < q := hp.trans hpq
  have hSum := primeSum_mono_base hp.le hpq.le k
  have hden : p * primeSum p k < q * primeSum q k := by
    calc
      p * primeSum p k < q * primeSum p k :=
        mul_lt_mul_of_pos_right hpq (primeSum_pos hp k)
      _ ≤ q * primeSum q k := mul_le_mul_of_nonneg_left hSum hq.le
  have hinv := one_div_lt_one_div_of_lt (mul_pos hp (primeSum_pos hp k)) hden
  unfold primeIncrement
  linarith only [hinv]

/-- The parameter threshold decreases strictly with the base as well as with
its exponent index. This is stated on positive real bases greater than one. -/
lemma primeThreshold_strictAnti_base (k : ℕ) :
    StrictAntiOn (fun p : ℝ => primeThreshold p k) (Set.Ioi 1) := by
  intro p hp q hq hpq
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hNum : Real.log (primeIncrement q k) < Real.log (primeIncrement p k) :=
    Real.log_lt_log (primeIncrement_pos hq0 k) (primeIncrement_lt_of_lt_base hp0 hpq k)
  calc
    primeThreshold q k < Real.log (primeIncrement p k) / Real.log q :=
      div_lt_div_of_pos_right hNum (Real.log_pos hq)
    _ ≤ primeThreshold p k :=
      div_le_div_of_nonneg_left (Real.log_nonneg (one_lt_primeIncrement hp0 k).le)
        (Real.log_pos hp) (Real.log_le_log hp0 hpq.le)

/-- An exponent is optimal exactly when the parameter lies between its two
adjacent thresholds; at exponent zero there is only an upper transition. -/
theorem primePowerWeight_maximal_iff_threshold {p : ℝ} (hp : 1 < p) (ε : ℝ) (a : ℕ) :
    (∀ k : ℕ, primePowerWeight p ε k ≤ primePowerWeight p ε a) ↔
      primeThreshold p a ≤ ε ∧ (a = 0 ∨ ε ≤ primeThreshold p (a - 1)) := by
  rw [primePowerWeight_maximal_iff (zero_lt_one.trans hp) ε a,
    primeIncrement_le_rpow_iff hp, rpow_le_primeIncrement_iff hp]

/-- The threshold characterization for the arithmetic weight at a prime. -/
theorem sigmaWeight_prime_power_maximal_iff_threshold {p : ℕ}
    (hp : p.Prime) (ε : ℝ) (a : ℕ) :
    (∀ k : ℕ, sigmaWeight ε (p ^ k) ≤ sigmaWeight ε (p ^ a)) ↔
      primeThreshold (p : ℝ) a ≤ ε ∧
        (a = 0 ∨ ε ≤ primeThreshold (p : ℝ) (a - 1)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [sigmaWeight_prime_power_maximal_iff hp ε a,
    primeIncrement_le_rpow_iff hpR, rpow_le_primeIncrement_iff hpR]

/-- The complete prime-by-prime parameter characterization, without a
uniqueness assumption and without invoking the Riemann hypothesis. -/
theorem isColossallyAbundantFor_iff_thresholds {ε : ℝ} {n : ℕ} :
    IsColossallyAbundantFor ε n ↔
      0 < ε ∧ 0 < n ∧ ∀ p : ℕ, p.Prime →
        primeThreshold (p : ℝ) (n.factorization p) ≤ ε ∧
          (n.factorization p = 0 ∨ ε ≤ primeThreshold (p : ℝ) (n.factorization p - 1)) := by
  rw [isColossallyAbundantFor_iff_primePower_maxima]
  constructor
  · rintro ⟨hε, hn, hLocal⟩
    exact ⟨hε, hn, fun p hp =>
      (sigmaWeight_prime_power_maximal_iff_threshold hp ε _).mp (hLocal p hp)⟩
  · rintro ⟨hε, hn, hLocal⟩
    exact ⟨hε, hn, fun p hp =>
      (sigmaWeight_prime_power_maximal_iff_threshold hp ε _).mpr (hLocal p hp)⟩

lemma primeSum_ge_succ {p : ℝ} (hp : 1 ≤ p) (k : ℕ) :
    (k : ℝ) + 1 ≤ primeSum p k := by
  calc
    (k : ℝ) + 1 = ∑ i ∈ range (k + 1), (1 : ℝ) := by simp
    _ ≤ primeSum p k := Finset.sum_le_sum fun i _ => one_le_pow₀ hp

/-- For a positive parameter, some adjacent ratio is at most one. No limit
or existence of a global maximizing integer is assumed in this lemma. -/
theorem exists_primeIncrement_le_rpow {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    ∃ k : ℕ, primeIncrement p k ≤ p ^ ε := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hδ : 0 < p ^ ε - 1 := sub_pos.mpr (Real.one_lt_rpow hp hε)
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (p ^ ε - 1))
  have hMul : 1 < (k : ℝ) * (p ^ ε - 1) := (div_lt_iff₀ hδ).mp hk
  have hSum : (k : ℝ) ≤ primeSum p k := by
    linarith only [primeSum_ge_succ hp.le k]
  have hProd : primeSum p k ≤ p * primeSum p k := by
    calc
      primeSum p k = 1 * primeSum p k := by ring
      _ ≤ p * primeSum p k := mul_le_mul_of_nonneg_right hp.le (primeSum_pos hp0 k).le
  have hScaled := mul_le_mul_of_nonneg_right (hSum.trans hProd) hδ.le
  have hMain : 1 < (p ^ ε - 1) * (p * primeSum p k) := by
    nlinarith only [hMul, hScaled]
  have hInv : 1 / (p * primeSum p k) < p ^ ε - 1 :=
    (div_lt_iff₀ (mul_pos hp0 (primeSum_pos hp0 k))).mpr hMain
  refine ⟨k, ?_⟩
  unfold primeIncrement
  linarith only [hInv]

/-- Every base greater than one has an optimal exponent for a positive
parameter. The proof chooses the first nonincreasing adjacent step. -/
theorem exists_primePowerWeight_maximizer {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    ∃ a : ℕ, ∀ k : ℕ, primePowerWeight p ε k ≤ primePowerWeight p ε a := by
  classical
  have hExists := exists_primeIncrement_le_rpow hp hε
  let a := Nat.find hExists
  refine ⟨a, (primePowerWeight_maximal_iff (zero_lt_one.trans hp) ε a).mpr ?_⟩
  refine ⟨Nat.find_spec hExists, ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    exact (not_le.mp (Nat.find_min hExists (by omega : a - 1 < a))).le

/-- An optimal local exponent exists at every prime. -/
theorem exists_sigmaWeight_prime_power_maximizer {p : ℕ} (hp : p.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℕ, ∀ k : ℕ, sigmaWeight ε (p ^ k) ≤ sigmaWeight ε (p ^ a) := by
  simp only [sigmaWeight_prime_pow hp]
  exact exists_primePowerWeight_maximizer (by exact_mod_cast hp.one_lt) hε

end LeanEval.NumberTheory.Lagarias.Robin
