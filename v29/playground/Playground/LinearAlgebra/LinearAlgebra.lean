import Mathlib

def v : Fin 3 → ℚ := ![0, 1, 0]
def w : Fin 3 → ℚ := ![1, 0, 1]


example (v w : Fin 3 → ℚ) : v + w = w + v := by
  ext i
  simp
  ring

def Orthogonal (v w : Fin 3 → ℚ) : Prop :=
  v ⬝ᵥ w = 0

#eval v ⬝ᵥ w
