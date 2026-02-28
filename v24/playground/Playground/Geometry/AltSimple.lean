import Mathlib


namespace AltSimple

def finiteAlternatingGroup (n : ℕ) := alternatingGroup (Fin n)

lemma alternatingGroup_simple (n : ℕ) (hn : 5 ≤ n) :
IsSimpleGroup (finiteAlternatingGroup n) := by
  sorry


end AltSimple