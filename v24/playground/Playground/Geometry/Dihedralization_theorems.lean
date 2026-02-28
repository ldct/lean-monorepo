import Playground.Geometry.Dihedralization


-- 4.12

namespace Dihedralization_theorems
open Dihedralization

example (G) [CommGroup G] [Fintype G] (g : G)
: Dihedralization.mk .one g ∈ Subgroup.center (Dihedralization G) ↔ g^2 = 1 := by
  rw [ Subgroup.mem_center_iff ]
  constructor <;> intro hg
  · specialize hg ⟨ C2.neg, g ⟩
    simp_all +decide [ Dihedralization.mul_eq, act, sq ]
  · simp [sq] at hg
    have hg := inv_eq_of_mul_eq_one_right hg
    rintro ⟨ c, h ⟩
    simp +decide [ Dihedralization.mul_eq ]
    fin_cases c <;> simp [mul_comm, hg]


end Dihedralization_theorems