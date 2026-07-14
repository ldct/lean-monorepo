import Mathlib

lemma ndvd_two_then (z : ℕ) (hz : z ∣ 2) : z = 1 ∨ z = 2 := by
  have : z ∈ Nat.divisors 2 := by grind
  simp only [Nat.divisors_ofNat] at this
  grind

example {n : ℕ} : 2^n*3^n = 6^n := by
  rw [show 6 = 3 * 2 from rfl]
  apply Additive.ofMul.injective
  simp [-Nat.reduceMul]
  module

-- fails for AddGroup
lemma add_left_cancel_iff' {G} [AddCommGroup G] (a b c : G) : a + b = a + c ↔ b = c := by
  grind only
