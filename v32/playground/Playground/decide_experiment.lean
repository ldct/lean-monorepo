import Mathlib


namespace decide_experiment

theorem exists_involution : ∃ r : DihedralGroup 4, r ≠ 1 ∧ r * r = 1 := by decide

theorem exists_involution' : ¬ ∃ r : Multiplicative (ZMod 7), r ≠ 1 ∧ r * r = 1 := by decide

-- TODO(v31 port): `noncomputable def extract` was left incomplete in the
-- original source (no signature/body). Commented out so the module compiles.
-- noncomputable def extract


end decide_experiment