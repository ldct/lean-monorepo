import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace DihedralGroup

variable {n : ℕ}

-- The action of Dih_n on the vertexes of the regular n-polygon (represented as ZMod n)

def smul_n (g : DihedralGroup n) (p : ZMod n): (ZMod n) :=
  match g with
  | r i => i + p
  | sr j => -j -p

def g_act : DihedralGroup 6 := r 2
def f_act := smul_n g_act
#eval [0, 1, 2, 3, 4, 5].map f_act

theorem r0_mul_p (p : ZMod n) : (smul_n (r 0) p) = p := by
  rw [smul_n]
  ring

instance (n : ℕ): MulAction (DihedralGroup n) (ZMod n) where
  smul := smul_n
  one_smul := by
    intro b
    apply r0_mul_p

  mul_smul := by
    rintro (_ | _) (_ | _) p -- intro and immediately case analysis to get 4 cases
    <;> simp [HSMul.hSMul, smul_n] <;> ring_nf

-- The action of Dih_n on the faces of the regular n-polygon (represented as ZMod 2)

def smul_2 (g : DihedralGroup n) (p : ZMod 2): (ZMod 2) :=
  match g with
  | r _ => p
  | sr _ => p+1

theorem r0_mul_p' (p : ZMod 2) : (smul_2 (r (0: ZMod n)) p) = p := by
  rw [smul_2]

instance (n : ℕ): MulAction (DihedralGroup n) (ZMod 2) where
  smul := smul_2
  one_smul := by
    intro b
    simp [HSMul.hSMul]

    apply r0_mul_p'

  mul_smul := by
    rintro (g1 | g1) (g2 | g2) p
    <;> simp [HSMul.hSMul, smul_2] <;> ring_nf
    norm_num
    rfl
