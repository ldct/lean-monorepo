import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

-- The action of Dih_n on the vertexes of the regular n-polygon (represented as ZMod n)

def smul_helper (g : DihedralGroup n) (p : ZMod n): (ZMod n) :=
  match g with
  | r i => i + p
  | sr j => -j -p

def g : DihedralGroup 6 := r 2
def f := smul_helper g
#eval [0, 1, 2, 3, 4, 5].map f

theorem test (p : ZMod n) : (smul_helper (r 0) p) = p := by
  rw [smul_helper]
  ring

instance (n : ℕ): MulAction (DihedralGroup n) (ZMod n) where
  smul := smul_helper
  one_smul := by
    intro b
    apply test

  mul_smul := by
    rintro (g1 | g1) (g2 | g2) p

    simp only [HSMul.hSMul]
    simp only [smul_helper, r_mul_r]
    ring

    simp only [HSMul.hSMul, smul_helper]
    simp only [r_mul_sr, neg_sub]
    ring

    simp only [HSMul.hSMul, smul_helper]
    simp only [sr_mul_r, neg_add_rev]
    ring

    simp only [HSMul.hSMul, smul_helper]
    simp only [sr_mul_sr]
    ring
