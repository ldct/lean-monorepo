import Mathlib

-- Note that this casts `rotations` to a type

namespace rotationsAreCyclic

example (n : ℕ) : IsCyclic (rotations n) := by
  use ⟨ DihedralGroup.r 1, by use 1 ⟩
  sorry


end rotationsAreCyclic