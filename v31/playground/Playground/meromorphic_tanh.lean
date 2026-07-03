import Mathlib

@[fun_prop]
lemma meromorphic_tanh : Meromorphic Complex.tanh := fun z ↦ by
  fun_prop [Complex.tanh]

lemma meromorphic_tanh' (z : ℂ) : MeromorphicAt Complex.tanh z := by
  fun_prop
