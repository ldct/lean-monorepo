import Mathlib

def nℤ (n : ℤ) : Ideal ℤ where
  carrier := { n * i | i : ℤ }
  add_mem' ha hb := by
    simp at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    ring
  zero_mem' := by
    use 0
    norm_num
  smul_mem' c d hx := by
    simp at hx
    obtain ⟨ n, rfl ⟩ := hx
    use c * n
    grind [Int.zsmul_eq_mul]

example : Nonempty ((ℤ ⧸ nℤ 2) ≃+* (ZMod 2)) := by sorry
