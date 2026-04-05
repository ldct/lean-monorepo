import Mathlib

/-- Demonstrations of equivalence relations, via Setoids -/

structure Point where
  x : ℝ
  y : ℝ

instance Point.instSetoid : Setoid Point where
  r a b := a.x = b.x
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by grind
    }

def Q := Quotient Point.instSetoid

/- The canonical Equiv between `Q` and `ℝ`-/
def myEquiv : Q ≃ ℝ where
  toFun := Quotient.lift Point.x fun _ _ h => h
  invFun r := Quotient.mk _ ⟨r, 0⟩
  left_inv q :=
    Quotient.inductionOn q fun p => Quotient.sound (show Point.instSetoid.r ⟨p.x, 0⟩ p by rfl)
  right_inv r := by simp [Quotient.lift_mk]
