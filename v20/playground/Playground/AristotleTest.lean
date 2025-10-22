import Mathlib

open Polynomial

theorem my_favorite_theorem {P : ℤ[X]} (hP : P.degree > 0)
    (hP0 : P.eval 0 ≠ 0) (a : ℕ → ℤ) (ha : ∀ i j, i > 0 → j > 0 → i ≠ j → P.eval (i - j) ∣ a i - a j) :
    ∃ c, ∀ n > 0, a n = c := by
    sorry
