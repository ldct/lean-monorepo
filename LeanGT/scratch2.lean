import Mathlib.Tactic

def d : ℕ → ℕ
| m => (Nat.divisors m).card
