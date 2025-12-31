import Mathlib

#check Functor

abbrev MyTypes := [Fin 2, Fin 3, Fin 5]

#eval Fintype.card (Fin 2)

#eval MyTypes.map (fun x ↦ Fintype.card x)
