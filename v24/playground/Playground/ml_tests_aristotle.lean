/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

The following was proved by Aristotle:

- example (a b k : ℝ) (k_pos : k ≠ 0) (eq : k*a = k*b)
: a = b

- example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2

- example (a b : ℕ) (h1 : a < b) : (2^a < 2^b)

- example
  (k : ℕ) (b : ℕ → ℝ)
:  ∑ x ∈ Finset.range (2 ^ (k + 2) - 1), b (x + 1)
  = ∑ x ∈ Finset.range (2 ^ (k + 1) - 1), b (x + 1)
  + ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1)

- example (m : ℕ) : ∃ k : ℕ, m ≤ 2^(k+1) - 1

- example (m : ℕ) : ∃ k : ℕ, m ≤ 2^(k+1) - 300

- example (m : ℕ)
: ∑ i ∈ Finset.range m, (1:ℝ) / (i + (1: ℝ)) ^ 2 ≤ ∑ i ∈ Finset.range m, if i = 0 then 1 else 1 / (i + (1: ℝ)) * (1 / i)

- example (x y : ℝ )
  (hp : (x+y)^2 > 0)
  (h' : 4 * x * y ≤ (x + y) ^ 2) :
    x*y/(x+y)^2 ≤ 1 / 4

- example
  (f : ℕ → ℝ)
: ∑ x ∈ Finset.range 4, f x = f 0 + f 1 + f 2 + f 3

- example (L : ℝ) (B : ℕ) : ∃ bad_n : ℕ, (L+1) < bad_n ∧ B < bad_n

- example (n : ℕ) (h : 0 < n)
: √(2 * (2 * n) * π) * ((2 * n) / rexp 1) ^ (2 * n) /
  (√(2 * n * π) * (n / rexp 1) ^ n) ^ 2
  = 4 ^ n / √(π * (n : ℝ))

- theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ))
-/

import Mathlib


example (a b k : ℝ) (k_pos : k ≠ 0) (eq : k*a = k*b)
: a = b := by
  -- Since $k \neq 0$, we can divide both sides of the equation $k * a = k * b$ by $k$ to get $a = b$.
  apply mul_left_cancel₀ k_pos eq

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  -- By contradiction, assume $t < 2$.
  by_contra h_contra; push_neg at h_contra; nlinarith

example (a b : ℕ) (h1 : a < b) : (2^a < 2^b) := by
  -- Since $a < b$, we have $2^a < 2^b$ by the strict monotonicity of the exponential function.
  apply pow_lt_pow_right₀; norm_num; exact h1

-- 1/1
theorem ttt
  (k : ℕ) (b : ℕ → ℝ)
: (∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), 1) * b (2 ^ (k + 1))
  = (∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (2 ^ (k + 1))) := by
  simp

-- 0/16
example
  (k : ℕ) (b : ℕ → ℝ)
:  ∑ x ∈ Finset.range (2 ^ (k + 2) - 1), b (x + 1)
  = ∑ x ∈ Finset.range (2 ^ (k + 1) - 1), b (x + 1)
  + ∑ x ∈ Finset.Ico (2 ^ (k + 1) - 1) (2 ^ (k + 2) - 1), b (x + 1)
:= by
  -- Apply the fact that Finset.sum is additive over adjacent ranges.
  rw [Finset.sum_range_add_sum_Ico];
  -- Since $2^{k+1} \leq 2^{k+2}$, subtracting 1 from both sides preserves the inequality.
  apply Nat.sub_le_sub_right; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

-- 1/16
example (m : ℕ) : ∃ k : ℕ, m ≤ 2^(k+1) - 1 := by
  -- By choosing $k = m$, we have $2^{m+1} - 1 \geq m$.
  use m;
  exact Nat.le_sub_one_of_lt ( Nat.recOn m ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith )

-- 1/16
example (m : ℕ) : ∃ k : ℕ, m ≤ 2^(k+1) - 300 := by
  -- We can prove this using properties of logarithms.
  use Nat.log 2 (m + 300);
  exact le_tsub_of_add_le_right ( by linarith [ Nat.lt_pow_of_log_lt one_lt_two ( by linarith : Nat.log 2 ( m + 300 ) < Nat.log 2 ( m + 300 ) + 1 ) ] )

-- 0/16
example (m : ℕ)
: ∑ i ∈ Finset.range m, (1:ℝ) / (i + (1: ℝ)) ^ 2 ≤ ∑ i ∈ Finset.range m, if i = 0 then 1 else 1 / (i + (1: ℝ)) * (1 / i) := by
  gcongr ; aesop;
  rw [ ← mul_inv, inv_le_inv₀ ] <;> norm_cast <;> nlinarith [ Nat.pos_of_ne_zero h ]

-- 1/1
example (x y : ℝ )
  (hp : (x+y)^2 > 0)
  (h' : 4 * x * y ≤ (x + y) ^ 2) :
    x*y/(x+y)^2 ≤ 1 / 4 := by
      -- By dividing both sides of the inequality $4 * x * y ≤ (x + y)^2$ by $(x + y)^2$, we get $x * y / (x + y)^2 ≤ 1 / 4$.
      rw [div_le_iff₀ hp] at *; linarith [h']

-- 1/1
example
  (f : ℕ → ℝ)
: ∑ x ∈ Finset.range 4, f x = f 0 + f 1 + f 2 + f 3 := by
  -- Apply the Finset.sum_range_succ lemma twice to break down the sum into individual terms.
  simp [Finset.sum_range_succ]

-- 0/16
example (L : ℝ) (B : ℕ) : ∃ bad_n : ℕ, (L+1) < bad_n ∧ B < bad_n := by
  exact ⟨ ⌊L + 1⌋₊ + B + 1, by push_cast; linarith [ Nat.lt_floor_add_one ( L + 1 ) ], by linarith ⟩

open Real

example (n : ℕ) (h : 0 < n)
: √(2 * (2 * n) * π) * ((2 * n) / rexp 1) ^ (2 * n) /
  (√(2 * n * π) * (n / rexp 1) ^ n) ^ 2
  = 4 ^ n / √(π * (n : ℝ)) := by
  -- Combine and simplify the constants and exponents in the denominator.
  field_simp [pow_mul]
  ring;
  simp +zetaDelta at *;
  -- Combine like terms and simplify the expression.
  ring_nf;
  norm_num [ pow_mul', Real.pi_pos.le ] ; ring

theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ)) := by
  have h_identity : (Nat.choose (n + k + 1) n : ℚ) = (Nat.choose (n + k) n : ℚ) * (n + k + 1) / (k + 1) ∧ (Nat.choose (n + k + 1) (n + 1) : ℚ) = (Nat.choose (n + k) n : ℚ) * (n + k + 1) / (n + 1) := by
    field_simp;
    norm_cast;
    constructor <;> nlinarith [ Nat.succ_mul_choose_eq ( n + k ) n, Nat.succ_mul_choose_eq ( n + k + 1 ) n, Nat.choose_succ_succ ( n + k ) n, Nat.choose_succ_succ ( n + k + 1 ) n ];
  aesop;
  -- Combine and simplify the fractions on the right-hand side.
  field_simp
  ring