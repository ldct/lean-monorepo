import LeanGT.Analysis.AlgebraicLimit
import LeanGT.Analysis.InfiniteSums
import LeanGT.Analysis.Bounded
import Mathlib

-- The terms 1/i
def inv_nats (i : ℕ) : ℝ := (1 / (i+1):ℚ)
-- The nth harmonic number
def s := partialSums inv_nats

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

-- Divergence of the harmonic series

theorem s_unbounded_formula (k : ℕ) : s (2^k) ≥ 1 + (k:ℝ)/2 := by
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

theorem s_unbounded : ¬ (Bounded s) := by
  intro s_bdd
  cases' s_bdd with B hB

  have : ∃ k : ℕ, 1 + (k:ℝ)/2 ≥ B := by
    let B' := ⌈B⌉
    have : 0 ≤ B' := Int.le_of_lt (Int.ceil_pos.mpr hB.left)
    lift B' to ℕ using this with B'' hB''
    use 2*B''
    push_cast
    have : (B':ℝ) = B'' := by exact congrArg Int.cast (Eq.symm hB'')
    rw [←this]
    unfold B'
    field_simp
    have : B ≤ ⌈B⌉ := by exact Int.le_ceil B
    linarith

  cases' this with k hk

  have s_2k := s_unbounded_formula k

  have s_2k_bdd := lt_of_abs_lt (hB.right (2^k))
  have s_2k_large : s (2^k) ≥ B := by exact Preorder.le_trans B (1 + ↑k / 2) (s (2 ^ k)) hk s_2k

  linarith

-- Example 2.4.5: The harmonic series diverges
theorem s_diverges : ¬ (Summable' inv_nats) := by
  intro h
  unfold Summable' at h
  rw [show partialSums inv_nats = s by rfl] at h
  exact s_unbounded (ConvergesThenBounded h)

def condense (a : ℕ → ℝ) : (ℕ → ℝ):= fun (i : ℕ) ↦
  2^i * a (2^i)

-- b₁ + 2b₂ + 4b₄ + 8b₈ + ...

example (b : ℕ → ℝ) : condense b 0 = b 1 := by
  simp [condense]

example (b : ℕ → ℝ) : condense b 1 = 2 * b 2 := by
  simp [condense]

example (b : ℕ → ℝ) : condense b 2 = 4 * b 4 := by
  simp [condense]
  norm_num

example (b : ℕ → ℝ) : condense b 3 = 8 * b 8 := by
  simp [condense]
  norm_num

theorem a_le_2_pow_a (a : ℕ) : a ≤ 2^a := by
  induction a with
  | zero => norm_num
  | succ n IH =>
    rw [show 2 ^ (n+1) = 2^n * 2 by omega]
    have : 1 ≤ 2^n := Nat.one_le_two_pow
    linarith

-- cauchy condensation test 2.4.6
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


  -- Let sm = b1+b1+…bm
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

  apply MCT

  exact monotone_psum_of_pos b_pos

  texify

  -- We need to show that sm is bounded. The bound used in the book is sm ≤ tk ≤ M where k is to be defined.
  use (b 0) + M
  intro m

  -- We have fixed m. Let k be large enough to ensure m ≤ 2^{k+1}-1

  have : ∃ k : ℕ, m ≤ 2^(k+1) - 1 := by
    use m
    -- idea: tactic to check m=0, m=1, ...
    sorry

  cases' this with k hk

  have c1 : s m ≤ s (2^(k+1) - 1) := by
    have sm : Monotone s := monotone_psum_of_pos fun i ↦ b_pos (i + 1)
    apply sm
    linarith

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
      -- texify
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
        -- texify
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive _ _ _
      rw [this]
      clear this
      -- texify
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

      have : ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1) ≤ ∑ i ∈ Finset.Ico (k + 1) (k + 2), 2 ^ i * b (2 ^ i) := by
        rw [Nat.Ico_succ_singleton (k + 1)]
        simp
        -- texify
      linarith

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
