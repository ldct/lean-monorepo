import Mathlib

abbrev DihedralProduct (n : ℕ) : Type :=
  Multiplicative (ZMod 2) × DihedralGroup n

example : Nonempty
  ((DihedralGroup 6) ≃* (DihedralProduct 3)) := by
  sorry

example {n : ℕ} (hn1 : 6 ≤ n) (hn2 : ∃ k, n = 4 * k + 2): Nonempty
  ((DihedralGroup n) ≃* (DihedralProduct (n/2))) := by
  sorry
