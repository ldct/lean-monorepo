import Mathlib

#check AddGroup.ofLeftAxioms

instance : AddGroup ℤ := AddGroup.ofLeftAxioms (by
  intro a b c
  grind
) (by
  intro a
  grind
) (by
  intro a
  grind
)
