import Mathlib


namespace AltCard

/-
The cardinality of the alternating group is n!/2
-/
def finiteAlternatingGroup (n : ℕ) := alternatingGroup (Fin n)

lemma card_finiteAlternatingGroup (n : ℕ) (hn : 5 ≤ n) :
Nat.card (finiteAlternatingGroup n) = (n.factorial / 2) := by
  sorry


end AltCard