import Mathlib

example (f g : ℝ → ℝ) (h : f = g) : sorry := by
  have h' := congr(($h 0)^2 + 1)
  sorry

def f : Fin 2 → Fin 2
  | 0 => 0
  | 1 => 1

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

abbrev O3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

#synth Group O3

@[push]
lemma test (a b c : ℕ) : a * (b + c) = a * b + a * c := by grind

@[push]
lemma test2 (a b c : ℕ) : (a + b) * c = a * c + b * c := by grind

example (a b c d : ℕ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  push (_ * _)
  ac_rfl
