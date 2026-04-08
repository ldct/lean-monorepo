import Mathlib


namespace ListsTest

abbrev MyTypes : List (Sigma Fintype) := [
  ⟨Fin 2, inferInstance⟩,
  ⟨Fin 3, inferInstance⟩,
  ⟨Fin 5, inferInstance⟩
]

-- [2, 3, 5]
#eval MyTypes.map (fun ⟨ty, inst⟩ => @Fintype.card ty inst)

abbrev MyTypes' : List FintypeCat := [
  FintypeCat.of (Fin 2),
  FintypeCat.of (Fin 3),
  FintypeCat.of (Fin 5)
]

-- [2, 3, 5]
-- In v29, FintypeCat uses Finite (not Fintype), so Fintype.card is noncomputable.
-- Use the Sigma-based approach above instead.


end ListsTest