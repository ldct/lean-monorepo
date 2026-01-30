/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6b000e84-5a02-471a-8ff2-34a7755985eb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example : (nℤ 2) + (nℤ 3) = (nℤ 1)
-/

import Mathlib


/-
# Example 2, the ideal nℤ ⊆ ℤ
-/
def nℤ (n : ℤ) : Ideal ℤ where
  carrier := { n * i | i : ℤ }
  add_mem' ha hb := by
    simp at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    ring
  zero_mem' := by
    use 0
    norm_num
  smul_mem' c d hx := by
    simp at hx
    obtain ⟨ n, rfl ⟩ := hx
    use c * n
    grind [Int.zsmul_eq_mul]

example : nℤ 1 = ⊤ := by
  ext i
  simp [nℤ]

example : nℤ 0 = ⊥ := by
  ext i
  simp [nℤ]

example : nℤ 2 = nℤ (-2) := by
  ext i
  simp [nℤ]
  constructor
  · rintro ⟨ j, rfl ⟩
    use -j
    ring
  · rintro ⟨ j, rfl ⟩
    use -j
    ring

example : (nℤ 2) + (nℤ 3) = (nℤ 1) := by
  simp
  ext i
  -- By Bezout's identity, since gcd(2, 3) = 1, there exist integers x and y such that 2x + 3y = 1.
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, 2 * x + 3 * y = 1 := by
    exists 2, -1;
  have h_mul : 2 * (x * i) + 3 * (y * i) = i := by
    linear_combination' hxy * i
  -- Since $2 * (x * i) + 3 * (y * i) = i$, we have $i \in nℤ 2 ⊔ nℤ 3$.
  have h_mem : i ∈ nℤ 2 ⊔ nℤ 3 := by
    exact h_mul ▸ Submodule.add_mem_sup ( ⟨ x * i, rfl ⟩ ) ( ⟨ y * i, rfl ⟩ );
  exact iff_of_true h_mem ( by exact ⟨ i, by ring ⟩ )
