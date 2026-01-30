/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c54ebd3f-b36a-458a-a4b4-99b741c5d3a4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example {n : ℤ} : nℤ n = Ideal.span {n}
-/

import Mathlib


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

abbrev ℤ2ℤ : Ideal ℤ := Ideal.span {2}

abbrev ℤ3ℤ : Ideal ℤ := Ideal.span {3}

example {n : ℤ} : nℤ n = Ideal.span {n} := by
  -- By definition of $n\mathbb{Z}$, we know that $n\mathbb{Z} = \{ n \cdot i \mid i \in \mathbb{Z} \}$.
  ext; simp [nℤ];
  -- By definition of ideal span, we know that $x \in \langle n \rangle$ if and only if $x$ is a multiple of $n$.
  simp [Ideal.mem_span_singleton];
  -- By definition of divisibility, $n \mid x$ if and only if there exists an integer $i$ such that $x = n * i$.
  simp [dvd_iff_exists_eq_mul_right];
  -- The equivalence follows directly from the symmetry of equality.
  simp [eq_comm]