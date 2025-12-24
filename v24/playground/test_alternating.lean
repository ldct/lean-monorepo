import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

#synth Group (Equiv.Perm (Fin 4))
#synth Fintype (Equiv.Perm (Fin 4))

abbrev AlternatingGroup (n : ℕ) := {σ : Equiv.Perm (Fin n) // Equiv.Perm.sign σ = 1}

def myMul (n : ℕ) (a b : AlternatingGroup n) : AlternatingGroup n := ⟨a.val * b.val, by
  rw [Equiv.Perm.sign_mul, a.prop, b.prop]
  norm_num
⟩

def myInv (n : ℕ) (a : AlternatingGroup n)
: AlternatingGroup n :=
  ⟨a.val⁻¹, by simp [Equiv.Perm.sign_inv, a.prop]⟩

theorem myInvMul (n : ℕ) (a : AlternatingGroup n) : (myMul n (myInv n a) a).val = 1 := by
  simp [myMul, myInv]

instance (n : ℕ) : Group (AlternatingGroup n) where
  mul := myMul n
  mul_assoc a b c := by
    simp [(· * ·)]
    rfl
  one := ⟨1, by simp ⟩
  one_mul a := by
    simp [(· * ·)]
    rfl
  mul_one a := by
    simp [(· * ·)]
    rfl
  inv := myInv n
  inv_mul_cancel a := by
    simp [(· * ·), myMul, myInv]
    exact Subtype.eq (myInvMul n a)


#synth Fintype (AlternatingGroup 4)
#synth Group (AlternatingGroup 4)

#eval Fintype.card (AlternatingGroup 4)
#eval Group.IsAbelian (AlternatingGroup 4)
#eval Group.FracInvolutions (AlternatingGroup 4)
#eval Group.CommutingFraction (AlternatingGroup 4)
