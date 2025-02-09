import LeanGT.Analysis.MonotoneConvergence
import Mathlib

-- Infinite sums

def partialSums (b : ℕ → ℝ) : (ℕ → ℝ) :=
  fun n ↦ ∑ i in Finset.range n, b i

def Summable' (b : ℕ → ℝ) : Prop := Converges (partialSums b)

-- The partial sum of a positive sequence is monotone
theorem monotone_psum_of_pos
  {a : ℕ → ℝ}
  (a_pos : ∀ i, 0 ≤ a i)
: Monotone (partialSums a) := by

  -- In a general preorder, proving monotonicity requires checking f(x) ≤ f(y) for all x ≤ y, but since ℕ is discrete, we can just check adjacent pairs x ≤ x+1
  apply monotone_nat_of_le_succ
  intro x
  unfold partialSums

  -- f(x) ≤ f(x+1) becomes ∑ range(x) ai ≤ ∑ range(x+1) ai, and we can rewrite the RHS as ∑ range(x) ai + (x-th term)
  rw [Finset.sum_range_succ_comm]

  -- Simp cancels common terms, leaving just 0 ≤ a x
  simp [a_pos x]

def inv_squares (i : ℕ) : ℝ := (1 / ((i+1)^2):ℚ)
def bassel := partialSums inv_squares

theorem monotone_bassel : Monotone bassel := by
  rw [bassel]
  apply monotone_psum_of_pos
  intro i
  rw [inv_squares]
  positivity

-- first inequality
theorem bb1 : bassel m ≤ ∑ i in Finset.range m, if i = 0 then 1 else (1/((i:ℝ)+1) * (1/i)) := by
  -- Unfold everything to ∑ and do a term-by-term comparison
  unfold bassel partialSums
  gcongr with i hi

  cases ne_or_eq i 0

  case h.inl i_ne_0 =>
    simp only [i_ne_0, reduceIte]
    unfold inv_squares
    push_cast
    rw [← (one_div_pow ((i:ℝ) + 1) 2)]
    rw [show (1 / ((i:ℝ) + 1))^2 = (1 / ((i:ℝ) + 1)) * (1 / ((i:ℝ) + 1)) by ring]
    gcongr _ * ?_
    gcongr
    linarith

  case h.inr i_eq_0 =>
    simp [i_eq_0]
    unfold inv_squares
    norm_num

theorem bb2 : (∑ i in Finset.range m, if i = 0 then 1 else (1/((i:ℝ)+1) * (1/i))) = ∑ i in Finset.range m, if i = 0 then 1 else ((1/i:ℝ) - 1/(i+1)) := by
  congr
  funext i

  cases ne_or_eq i 0
  case h.inl i_ne_0 =>
    simp [i_ne_0]
    field_simp
    ring

  case h.inr i_eq_0 =>
    simp [i_eq_0]

theorem bb3 (hm : 1 ≤ m) : (∑ i in Finset.range m, if i = 0 then 1 else ((1/i:ℝ) - 1/(i+1))) = 2 - 1/(m:ℝ) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show Finset.range 1 = {0} by decide]
    simp
    norm_num
  | succ n t IH =>
    rw [Finset.sum_range_succ_comm]
    simp only [show n ≠ 0 by positivity]
    rw [IH]
    simp

theorem final : bassel m ≤ 2 := by
  cases Nat.le_total 1 m

  case inl hm => calc
    bassel m ≤ ∑ i in Finset.range m, if i = 0 then 1 else (1/((i:ℝ)+1) * (1/i)) := bb1
    _ = ∑ i in Finset.range m, if i = 0 then 1 else ((1/i:ℝ) - 1/(i+1)) := bb2
    _ = 2 - 1/(m:ℝ) := bb3 hm
    _ ≤ 2 := by
      have : 0 < 1/(m:ℝ) := by positivity
      linarith

  case inr hm =>
    have : m = 0 ∨ m = 1 := by exact Nat.le_one_iff_eq_zero_or_eq_one.mp hm

    cases this

    case inl m_eq_0 =>
      rw [m_eq_0]
      unfold bassel partialSums
      simp

    case inr m_eq_1 =>
      rw [m_eq_1]
      unfold bassel partialSums inv_squares
      simp

-- Example 2.4.4: ∑ 1/n^2 converges to some (presently unknown) limit
theorem c1 : Summable' inv_squares := by
  rw [Summable']
  apply MCT
  exact monotone_bassel
  use 2
  intro n
  exact final

def inv_nats (i : ℕ) : ℝ := (1 / (i+1):ℚ)

-- The nth harmonic number
def s := partialSums inv_nats

example (f : ℕ → ℝ) (h1 : a ≤ b) (h2 : b ≤ c): (∑ i ∈ Finset.Ico a c, f i) = ∑ i ∈ Finset.Ico a b, f i +  ∑ i ∈ Finset.Ico b c, f i := by
  exact Eq.symm (Finset.sum_Ico_consecutive f h1 h2)

theorem e1 (k : ℕ) : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats i) ≥ (∑ _ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats (2^(k+1)-1)) := by
  gcongr with i hi
  unfold inv_nats
  simp
  gcongr
  norm_cast
  simp [Finset.mem_Ico] at hi
  linarith

theorem e2 (k : ℕ) : (∑ _ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats (2^(k+1)-1)) = (1/2) := by

  have : 2^(k + 1) - 2^k = 2^k := by
    simp [Nat.pow_succ', show 2*2^k = 2^k+2^k by omega]

  simp
  unfold inv_nats
  simp
  rw [this]
  field_simp
  ring




theorem h_div (k : ℕ) : s (2^k) ≥ 1 + (k:ℝ)/2 := by
  induction k with
  | zero =>
    simp
    unfold s partialSums inv_nats
    simp
  | succ k IH =>
    unfold s partialSums
    unfold s partialSums at IH
    rw [congrFun Finset.range_eq_Ico (2 ^ (k + 1))]

    rw [← Finset.sum_Ico_consecutive inv_nats (show 0 ≤ 2^k by positivity) (show 2^k ≤ 2^(k+1) by gcongr <;> omega)]

    have : (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats i) ≥ 1/2 := by
      calc
        (∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats i) ≥ (∑ _ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats (2^(k+1)-1)) := e1 k
        _ = 1/2 := e2 k

    have t := calc
      (∑ i ∈ Finset.Ico 0 (2 ^ k), inv_nats i + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats i) = (∑ i ∈ Finset.range (2 ^ k), inv_nats i + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats i) := by
        congr
        rw [congrFun Finset.range_eq_Ico]
      (∑ i ∈ Finset.range (2 ^ k), inv_nats i + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats i) ≥  (1 + k/2) + ∑ i ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), inv_nats i := by
        gcongr
      _ ≥ 1 + k/2 + 1/2 := by
        gcongr
      _ = 1 + (k+1)/2 := by ring

    push_cast at t
    push_cast
    exact t
