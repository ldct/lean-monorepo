import Mathlib


namespace MinimalAxioms

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


end MinimalAxioms