import Mathlib

abbrev D40 := DihedralGroup 40

abbrev Q := D40 ⧸ (Subgroup.center D40)

abbrev g : D40 := .r 1

abbrev g' : Q := ⟦g⟧

abbrev l := g' * g'

#check l

#eval g * g
