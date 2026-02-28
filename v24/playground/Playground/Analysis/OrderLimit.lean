import Playground.Analysis.AlgebraicLimit
import Mathlib

-- Theorem 2.3.4.i (Order Limit Theorem)

namespace OrderLimit
open AlgebraicLimit TendsTo

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


end OrderLimit