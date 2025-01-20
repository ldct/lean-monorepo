import LeanGT.Analysis.AlgebraicLimit
import MathLib


-- Theorem 2.3.4.i (Order Limit Theorem)
theorem tendsTo_pos
  {a : ℕ → ℝ}
  {A : ℝ}
  (a_pos : ∀ n, 0 ≤ a n)
  (a_tendsTo_A : TendsTo a A)
: 0 ≤ A := by
  by_contra a_neg
  have a_neg : A < 0 := lt_of_not_ge a_neg
  cases' (a_tendsTo_A (-A) (by linarith)) with N hN
  specialize hN N (by linarith)
  rw [abs_lt] at hN
  simp at hN
  cases' hN with h1 h2
  have : a N < 0 := by linarith
  specialize a_pos N
  linarith

-- Theorem 2.3.4.ii
theorem tendsTo_le
  {a b : ℕ → ℝ}
  {A B : ℝ}
  (a_le_b : ∀ n, a n ≤ b n)
  (a_tendsTo_A : TendsTo a A)
  (b_tendsTo_B : TendsTo b B)
: A ≤ B := by
  let c := fun n ↦ (b n) + (-1)*(a n)
  have c_tendsTo : TendsTo c (B - A) := by
    apply tendsTo_sum
    exact b_tendsTo_B
    rw [show -A = (-1) * A by ring]
    apply tendsTo_mul_constant_nz
    norm_num
    exact a_tendsTo_A
  have c_pos : ∀ n, 0 ≤ c n := by
    intro n
    specialize a_le_b n
    unfold c
    linarith
  have : 0 ≤ B - A := by exact tendsTo_pos c_pos c_tendsTo
  linarith

-- Theorem 2.3.4.iii
theorem tendsTo_le_const
  {b : ℕ → ℝ}
  {C B : ℝ}
  (C_le_b : ∀ n, C ≤ b n)
  (b_tendsTo_B : TendsTo b B)
: C ≤ B := by
  apply tendsTo_le C_le_b
  exact tendsTo_const C
  exact b_tendsTo_B

-- Theorem 2.3.4.iii (other case)
theorem tendsTo_const_le
  {a : ℕ → ℝ}
  {A C : ℝ}
  (a_le_C : ∀ n, a n ≤ C)
  (a_tendsTo_A : TendsTo a A)
: A ≤ C := by
  apply tendsTo_le a_le_C
  exact a_tendsTo_A
  exact tendsTo_const C

-- Monotone Convergence Theorem
theorem MCT
  {a : ℕ → ℝ}
  {B : ℝ}
  (a_inc : Monotone a)
  (a_bdd : ∀ n, a n ≤ B)
: TendsTo a (sSup { a n | n : ℕ}) := by
  let as := { a n | n : ℕ}
  let s := sSup as

  have as_Bdd : BddAbove as := by
    use B
    unfold upperBounds
    rintro e ⟨ n, hn ⟩
    exact le_of_eq_of_le (Eq.symm hn) (a_bdd n)

  have as_Nonempty : as.Nonempty := by use (a 0), 0

  have s_IsLUB : IsLUB as s := by
    exact Real.isLUB_sSup as_Nonempty as_Bdd

  intro ε hε

  have s_is_ub : s ∈ upperBounds as := by
    exact Set.mem_of_mem_inter_left s_IsLUB

  have : (s - ε) ∉ upperBounds as := by
    rw [IsLUB, IsLeast] at s_IsLUB
    have t := s_IsLUB.right
    unfold lowerBounds at t
    simp at t
    by_contra l_ε_ub
    specialize t l_ε_ub
    linarith

  unfold upperBounds at this
  simp at this
  cases' this with aN haN
  cases' haN with aN_in_s haN
  cases' aN_in_s with N hN
  rw [← hN] at haN
  use N
  intro n hn
  have : a N ≤ a n := a_inc hn
  rw [show sSup {x | ∃ n, a n = x} = s by exact rfl]
  rw [abs_lt]
  constructor
  linarith
  have : (a n) ∈ as := by use n
  have : a n ≤ s := by exact s_is_ub this
  linarith
