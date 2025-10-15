import Mathlib


/--
The snake lemma is a standard tool in homological algebra. The basic situation
is when we have a diagram as follows in an abelian category `C`, with exact rows:

```
    L₁.X₁ ⟶ L₁.X₂ ⟶ L₁.X₃ ⟶ 0
      │       │       │
      │v₁₂.τ₁ │v₁₂.τ₂ │v₁₂.τ₃
      ↓       ↓       ↓
0 ⟶ L₂.X₁ ⟶ L₂.X₂ ⟶ L₂.X₃
```

We shall think of this diagram as the datum of a morphism `v₁₂ : L₁ ⟶ L₂` in the
-/
example : 1 = 1 := by rfl

/--
```
       0        0         0
       │        │         │
… ───▶ X₁,i ──▶ X₁,j ─d─▶ X₁,k ──▶ …
       │        ↓ f       │
… ───▶ X₂,i ──d─▶ X₂,j ─▶ X₂,k ──▶ …
        │       │         │
… ───▶ X₃,i ───▶ X₃,j ──▶ X₃,k ──▶ …
        ↓       ↓         ↓
        0       0         0
```

Some theorem
-/
example : 1 = 1 := by rfl


example (a b k : ℝ) (k_pos : k ≠ 0) (eq : k*a = k*b)
: a = b := by
  sorry

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  sorry

example (a b : ℕ) (h1 : a < b) : (2^a < 2^b) := by
  sorry

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

-- 1/16
example (m : ℕ) : ∃ k : ℕ, m ≤ 2^(k+1) - 1 := by
  sorry

-- 1/16
example (m : ℕ) : ∃ k : ℕ, m ≤ 2^(k+1) - 300 := by
  sorry

-- 0/16
example (m : ℕ)
: ∑ i ∈ Finset.range m, (1:ℝ) / (i + (1: ℝ)) ^ 2 ≤ ∑ i ∈ Finset.range m, if i = 0 then 1 else 1 / (i + (1: ℝ)) * (1 / i) := by
  sorry

-- 1/1
example (x y : ℝ )
  (hp : (x+y)^2 > 0)
  (h' : 4 * x * y ≤ (x + y) ^ 2) :
    x*y/(x+y)^2 ≤ 1 / 4 := by sorry

-- 1/1
example
  (f : ℕ → ℝ)
: ∑ x ∈ Finset.range 4, f x = f 0 + f 1 + f 2 + f 3 := by
  sorry

-- 0/16
example (L : ℝ) (B : ℕ) : ∃ bad_n : ℕ, (L+1) < bad_n ∧ B < bad_n := by sorry

open Real

example (n : ℕ) (h : 0 < n)
: √(2 * (2 * n) * π) * ((2 * n) / rexp 1) ^ (2 * n) /
  (√(2 * n * π) * (n / rexp 1) ^ n) ^ 2
  = 4 ^ n / √(π * (n : ℝ)) := by

  field_simp [mul_pow, <- pow_mul, pow_mul, mul_comm]
  ring_nf
  norm_num [mul_comm (a := n), pow_mul, pi_nonneg]
  ac_rfl


theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ)) := by
  sorry
