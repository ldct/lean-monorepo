import Mathlib
import LeanTeXMathlib

def lhs (k : ℕ) : Finset ℕ := Finset.range k
def rhs (k : ℕ) : Finset ℕ := Finset.Ico k (k + 1)

#eval lhs 0
#eval rhs 0

example (k : ℕ) : lhs k ∪ rhs k = Finset.range (k + 1) := by
  unfold lhs rhs
  rw [Finset.range_eq_Ico]
  rw [Finset.Ico_union_Ico_eq_Ico]
  texify

example (k : ℕ) : Disjoint (lhs k) (rhs k) := by
  unfold lhs rhs
  rw [Finset.range_eq_Ico]
  exact?
