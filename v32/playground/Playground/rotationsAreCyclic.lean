import Mathlib

-- Note that this casts `rotations` to a type

namespace rotationsAreCyclic

def rotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := { DihedralGroup.r i | i : ZMod n }
  mul_mem' := by
    rintro a b ⟨ i1, rfl ⟩ ⟨ i2, rfl ⟩
    use i1 + i2
    rfl
  one_mem' := by
    use 0
    rfl
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    use -i
    rfl

example (n : ℕ) : IsCyclic (rotations n) := by
  use ⟨ DihedralGroup.r 1, by use 1 ⟩
  sorry


end rotationsAreCyclic