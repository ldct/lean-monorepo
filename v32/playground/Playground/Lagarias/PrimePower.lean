import Playground.Lagarias.ColossallyAbundant

/-!
# Prime-power factors and their exact maximizers

The adjacent ratio of the local weight is
`(1 + 1 / (p + ... + p^(k+1))) / p^epsilon`.
The numerator decreases strictly with `k`, so a pair of adjacent comparisons
characterizes a global maximizing exponent. This is the elementary content
behind the parameter inequalities in Caveney--Nicolas--Sondow,
*On SA, CA, and GA numbers*, arXiv:1112.6010, Section 2, equation (9).
-/

namespace LeanEval.NumberTheory.Lagarias.Robin

open Finset
open scoped ArithmeticFunction.sigma

/-- The geometric sum `1 + p + ... + p^k`. -/
noncomputable def primeSum (p : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), p ^ i

@[simp] lemma primeSum_zero (p : ℝ) : primeSum p 0 = 1 := by
  simp [primeSum]

lemma primeSum_succ (p : ℝ) (k : ℕ) :
    primeSum p (k + 1) = primeSum p k + p ^ (k + 1) := by
  exact Finset.sum_range_succ _ _

lemma primeSum_pos {p : ℝ} (hp : 0 < p) (k : ℕ) : 0 < primeSum p k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [primeSum_succ]
    exact add_pos ih (pow_pos hp _)

lemma primeSum_strictMono {p : ℝ} (hp : 0 < p) : StrictMono (primeSum p) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [primeSum_succ]
  linarith only [pow_pos hp (k + 1)]

lemma primeSum_succ_mul (p : ℝ) (k : ℕ) :
    primeSum p (k + 1) = p * primeSum p k + 1 := by
  change (∑ i ∈ range ((k + 1) + 1), p ^ i) = p * (∑ i ∈ range (k + 1), p ^ i) + 1
  rw [Finset.sum_range_succ']
  simp only [pow_succ', pow_zero, ← Finset.mul_sum]

/-- Real-valued local weight, defined also at nonprime positive real bases. -/
noncomputable def primePowerWeight (p ε : ℝ) (k : ℕ) : ℝ :=
  primeSum p k / (p ^ (1 + ε)) ^ k

@[simp] lemma primePowerWeight_zero (p ε : ℝ) : primePowerWeight p ε 0 = 1 := by
  simp [primePowerWeight]

lemma primePowerWeight_pos {p : ℝ} (hp : 0 < p) (ε : ℝ) (k : ℕ) :
    0 < primePowerWeight p ε k := by
  exact div_pos (primeSum_pos hp k) (pow_pos (Real.rpow_pos_of_pos hp _) _)

lemma sigmaWeight_prime_pow {p : ℕ} (hp : p.Prime) (ε : ℝ) (k : ℕ) :
    sigmaWeight ε (p ^ k) = primePowerWeight (p : ℝ) ε k := by
  have hden : ((p : ℝ) ^ k) ^ (1 + ε) = ((p : ℝ) ^ (1 + ε)) ^ k := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm,
      Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
  simp only [sigmaWeight_apply, ArithmeticFunction.sigma_one_apply_prime_pow hp,
    Nat.cast_sum, Nat.cast_pow, hden, primePowerWeight, primeSum]

/-- The part of the adjacent ratio independent of the parameter. Its denominator
is `p + ... + p^(k+1)`, not the geometric sum starting at one. -/
noncomputable def primeIncrement (p : ℝ) (k : ℕ) : ℝ :=
  1 + 1 / (p * primeSum p k)

@[simp] lemma primeIncrement_zero (p : ℝ) : primeIncrement p 0 = 1 + 1 / p := by
  simp [primeIncrement]

lemma one_lt_primeIncrement {p : ℝ} (hp : 0 < p) (k : ℕ) :
    1 < primeIncrement p k := by
  have h : 0 < 1 / (p * primeSum p k) := one_div_pos.mpr (mul_pos hp (primeSum_pos hp k))
  dsimp [primeIncrement]
  linarith only [h]

lemma primeIncrement_pos {p : ℝ} (hp : 0 < p) (k : ℕ) :
    0 < primeIncrement p k := lt_trans zero_lt_one (one_lt_primeIncrement hp k)

lemma primeIncrement_strictAnti {p : ℝ} (hp : 0 < p) : StrictAnti (primeIncrement p) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  have hden : p * primeSum p k < p * primeSum p (k + 1) :=
    mul_lt_mul_of_pos_left (primeSum_strictMono hp (Nat.lt_succ_self k)) hp
  have hinv := one_div_lt_one_div_of_lt (mul_pos hp (primeSum_pos hp k)) hden
  dsimp [primeIncrement]
  linarith only [hinv]

lemma primePowerWeight_succ_eq {p : ℝ} (hp : 0 < p) (ε : ℝ) (k : ℕ) :
    primePowerWeight p ε (k + 1) =
      primePowerWeight p ε k * (primeIncrement p k / p ^ ε) := by
  have hs : primeSum p k ≠ 0 := ne_of_gt (primeSum_pos hp k)
  have he : p ^ ε ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp ε)
  unfold primePowerWeight primeIncrement
  rw [primeSum_succ_mul, pow_succ, Real.rpow_add hp, Real.rpow_one]
  field_simp [ne_of_gt hp, hs, he]
  <;> ring

lemma primePowerWeight_le_succ_iff {p : ℝ} (hp : 0 < p) (ε : ℝ) (k : ℕ) :
    primePowerWeight p ε k ≤ primePowerWeight p ε (k + 1) ↔
      p ^ ε ≤ primeIncrement p k := by
  rw [primePowerWeight_succ_eq hp ε k]
  have hw := primePowerWeight_pos hp ε k
  have he := Real.rpow_pos_of_pos hp ε
  calc
    primePowerWeight p ε k ≤ primePowerWeight p ε k * (primeIncrement p k / p ^ ε) ↔
        primePowerWeight p ε k * 1 ≤ primePowerWeight p ε k * (primeIncrement p k / p ^ ε) := by
          rw [mul_one]
    _ ↔ 1 ≤ primeIncrement p k / p ^ ε := mul_le_mul_iff_of_pos_left hw
    _ ↔ p ^ ε ≤ primeIncrement p k := by rw [le_div_iff₀ he, one_mul]

lemma primePowerWeight_succ_le_iff {p : ℝ} (hp : 0 < p) (ε : ℝ) (k : ℕ) :
    primePowerWeight p ε (k + 1) ≤ primePowerWeight p ε k ↔
      primeIncrement p k ≤ p ^ ε := by
  rw [primePowerWeight_succ_eq hp ε k]
  have hw := primePowerWeight_pos hp ε k
  have he := Real.rpow_pos_of_pos hp ε
  calc
    primePowerWeight p ε k * (primeIncrement p k / p ^ ε) ≤ primePowerWeight p ε k ↔
        primePowerWeight p ε k * (primeIncrement p k / p ^ ε) ≤ primePowerWeight p ε k * 1 := by
          rw [mul_one]
    _ ↔ primeIncrement p k / p ^ ε ≤ 1 := mul_le_mul_iff_of_pos_left hw
    _ ↔ primeIncrement p k ≤ p ^ ε := by rw [div_le_iff₀ he, one_mul]

/-- A sequence that rises up to `a` and falls afterwards is bounded by its value
at `a`. Nonstrict comparisons retain both maximizers when an adjacent tie occurs. -/
lemma le_peak_of_adjacent_comparisons {f : ℕ → ℝ} {a : ℕ}
    (hUp : ∀ k : ℕ, k < a → f k ≤ f (k + 1))
    (hDown : ∀ k : ℕ, a ≤ k → f (k + 1) ≤ f k) :
    ∀ k : ℕ, f k ≤ f a := by
  have hUpRange : ∀ m n : ℕ, m ≤ n → n ≤ a → f m ≤ f n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ n hmn ih =>
      intro hn
      exact (ih (by omega)).trans (hUp n (by omega))
  have hDownRange : ∀ k : ℕ, a ≤ k → f k ≤ f a := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (hDown k hk).trans ih
  intro k
  by_cases h : k ≤ a
  · exact hUpRange k a h le_rfl
  · exact hDownRange k (by omega)

/-- Optimality is exactly the two adjacent comparisons. This proof does not
assume existence or uniqueness of a maximizing exponent. -/
theorem primePowerWeight_maximal_iff {p : ℝ} (hp : 0 < p) (ε : ℝ) (a : ℕ) :
    (∀ k : ℕ, primePowerWeight p ε k ≤ primePowerWeight p ε a) ↔
      primeIncrement p a ≤ p ^ ε ∧
        (a = 0 ∨ p ^ ε ≤ primeIncrement p (a - 1)) := by
  constructor
  · intro h
    refine ⟨(primePowerWeight_succ_le_iff hp ε a).mp (h (a + 1)), ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      apply (primePowerWeight_le_succ_iff hp ε (a - 1)).mp
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ a)] using h (a - 1)
  · rintro ⟨hNext, hPrev⟩
    apply le_peak_of_adjacent_comparisons
    · intro k hk
      apply (primePowerWeight_le_succ_iff hp ε k).mpr
      rcases hPrev with hzero | hPrev
      · omega
      · exact hPrev.trans ((primeIncrement_strictAnti hp).antitone (by omega : k ≤ a - 1))
    · intro k hk
      apply (primePowerWeight_succ_le_iff hp ε k).mpr
      exact ((primeIncrement_strictAnti hp).antitone hk).trans hNext

/-- Specialize the real local optimization theorem to the arithmetic weight. -/
theorem sigmaWeight_prime_power_maximal_iff {p : ℕ} (hp : p.Prime) (ε : ℝ) (a : ℕ) :
    (∀ k : ℕ, sigmaWeight ε (p ^ k) ≤ sigmaWeight ε (p ^ a)) ↔
      primeIncrement (p : ℝ) a ≤ (p : ℝ) ^ ε ∧
        (a = 0 ∨ (p : ℝ) ^ ε ≤ primeIncrement (p : ℝ) (a - 1)) := by
  simp only [sigmaWeight_prime_pow hp]
  exact primePowerWeight_maximal_iff (by exact_mod_cast hp.pos) ε a

end LeanEval.NumberTheory.Lagarias.Robin
