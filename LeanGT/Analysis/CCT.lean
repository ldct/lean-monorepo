import LeanGT.Analysis.AlgebraicLimit
import LeanGT.Analysis.InfiniteSums
import LeanGT.Analysis.Bounded
import LeanGT.Analysis.MonotoneConvergence
import Mathlib

-- Cauchy condensation test

-- The sequence b₁, 2b₂, 4b₄, 8b₈, ...
-- We will want to show that this is summable ↔ a is summable
def condense (a : ℕ → ℝ) : (ℕ → ℝ):= fun (i : ℕ) ↦
  2^i * a (2^i)

latex_pp_app_rules (const := HSMul.hSMul)
  | _, #[_, _, _, _, a, b] => do
    let a ← LeanTeX.latexPP a
    let b ← LeanTeX.latexPP b
    return "(" ++ a ++ " \\cdot " ++ b ++ ")" |>.resetBP .Infinity .Infinity

-- cauchy condensation test 2.4.6, hard direction
-- b₀ + b₁ ... converges iff b₁ + 2b₂ + 4b₄ + 8b₈ + ... converges
theorem cct1
  {b : ℕ → ℝ}
  (b_pos : ∀ n, 0 ≤ b n)
  (b_antitone : Antitone b)
  (c_summable : Summable' (condense b))
: Summable' b := by

  -- Let tm = ...
  let t := (fun i ↦ (partialSums (condense b) (i+1)))

  have : t 0 = b 1 := by
    unfold t partialSums condense
    simp

  have : t 1 = b 1 + 2 * b 2 := by
    unfold t partialSums condense
    rw [show Finset.range 2 = {0, 1} by decide]
    simp

  repeat clear this

  -- Let sm = b1+b2+…bm
  let s := partialSums (fun n ↦ b (n+1))

  have : s 0 = 0 := by
    unfold s partialSums
    simp

  have : s 1 = b 1 := by
    unfold s partialSums
    simp

  have : s 2 = b 1 + b 2 := by
    unfold s partialSums
    simp
    rw [show Finset.range 2 = {0, 1} by decide]
    simp

  repeat clear this

  unfold Summable' at c_summable
  have bdd := ConvergesThenBounded c_summable
  refold_let t at *
  cases' bdd with M hM
  cases' hM with M_pos M_bounds
  have M_bounds' : ∀ n, (partialSums (condense b) n) < M := by
    exact fun n ↦ lt_of_abs_lt (M_bounds n)

  clear M_bounds

  refine MCT ?bIncreasing ?bBounded

  case bIncreasing => exact monotone_psum_of_pos b_pos

  case bBounded =>
  use (b 0) + M
  intro m

  -- We have fixed m. Let k be large enough to ensure m ≤ 2^{k+1}-1

  have : ∃ k : ℕ, m ≤ 2^(k+1) - 1 := by
    use m
    -- idea: tactic to check m=0, m=1, ...
    induction m with
    | zero =>
      norm_num
    | succ m IH =>
      rw [show 2^(m+1+1) = 2^(m+1) + 2^(m+1) by ring]
      have : 1 ≤ 2^(m+1) := Nat.one_le_two_pow
      omega

  cases' this with k hk

  have c1 : s m ≤ s (2^(k+1) - 1) := by
    have sm : Monotone s := monotone_psum_of_pos fun i ↦ b_pos (i + 1)
    apply sm
    linarith

  -- The main argument: the partial sums of b, adding successively more powers of 2, is bounded by t
  have c2 (k' : ℕ): s (2^(k'+1) - 1) ≤ t k' := by
    induction k' with
    | zero =>
      norm_num
      unfold s t partialSums condense
      repeat rw [Finset.sum_range_succ]
      simp
    | succ k IH =>
      unfold s t partialSums condense
      unfold s t partialSums condense at IH
      simp
      simp at IH
      rw [show k + 1 + 1 = (k + 2) by ring] at *

      -- Write the LHS as (LHS of induction hypothesis) + something
      have :  ∑ x ∈ Finset.range (2 ^ (k + 2) - 1), b (x + 1)
        = ∑ x ∈ Finset.range (2 ^ (k + 1) - 1), b (x + 1)
        + ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1)
      := by
        rw [show Finset.range (2 ^ (k + 2) - 1) = Finset.range (2 ^ (k + 1) - 1) ∪ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1) by
          rw [Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico]
          positivity
          gcongr
          norm_num
          norm_num
        ]
        rw [Finset.sum_union]
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive _ _ _
      rw [this]
      clear this

      -- Write the RHS as (RHS of induction hypothesis) + something
      have : ∑ i ∈ Finset.range (k + 2), 2 ^ i * b (2 ^ i)
        = ∑ i ∈ Finset.range (k + 1), 2 ^ i * b (2 ^ i)
        + ∑ i ∈ Finset.Ico (k + 1) (k + 2), 2 ^ i * b (2 ^ i)
      := by
        -- texify
        rw [show Finset.range (k + 2) = Finset.range (k + 1) ∪ Finset.Ico (k + 1) (k + 2) by
          rw [Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico]
          positivity
          gcongr
          norm_num
        ]
        rw [Finset.sum_union, Finset.range_eq_Ico]
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive _ _ _
      rw [this]
      clear this

      suffices t : ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1) ≤ ∑ i ∈ Finset.Ico (k + 1) (k + 2), 2 ^ i * b (2 ^ i) from by linarith

      -- Now we are comparing a sum of 2^(k+1) terms with a single term of the condensed series.
      clear IH c_summable M_bounds'
      -- texify
      rw [Nat.Ico_succ_singleton (k + 1)]
      simp
      have : 2 ^ (k + 1) = ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), 1 := by
        rw [Finset.sum_const]
        simp
        rw [Nat.two_pow_succ (k + 1)]
        have rwl (t : ℕ) : t = t + t - 1 - (t - 1) := by omega
        exact rwl (2 ^ (k + 1))
      conv =>
        rhs
        lhs
        norm_cast
        rw [show 2 ^ (k + 1) = ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), 1 by
          rw [Finset.sum_const]
          simp
          rw [Nat.two_pow_succ (k + 1)]
          -- texify
          have rwl (t : ℕ) : t = t + t - 1 - (t - 1) := by omega
          exact rwl (2 ^ (k + 1))
        ]

      have ttt :
        (∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), 1) * b (2 ^ (k + 1))
        = (∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (2 ^ (k + 1))) := by
        rw [Finset.sum_const]
        rw [Finset.sum_const]
        simp

      texify

      norm_cast at ttt
      rw [ttt]
      clear ttt
      -- texify
      gcongr with i a
      simp at a
      cases' a with al ar
      -- texify
      exact b_antitone al


  specialize c2 k

  have c3 : s m ≤ t k := by linarith
  clear c1 c2 hk

  have c4 : t k ≤ M := by
    unfold t
    exact le_of_lt (M_bounds' (k + 1))

  have c5 : s m ≤ M := by linarith
  clear c3 c4


  unfold s at c5

  have (m' : ℕ) : (b 0) + partialSums (fun n ↦ b (n + 1)) m' = partialSums b (m' + 1) := by
    induction m' with
    | zero =>
      simp [partialSums]
    | succ m' IH =>
      rw [partialSums_succ]
      ring_nf
      rw [← add_assoc (b 0) _, IH]
      rw [partialSums_succ b (m' + 1)]

  specialize this m

  have l : partialSums b m ≤ partialSums b (m + 1) := by
    apply monotone_psum_of_pos
    exact fun i ↦ b_pos i
    omega

  linarith
