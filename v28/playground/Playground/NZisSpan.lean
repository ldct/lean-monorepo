import Mathlib


namespace NZisSpan

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

abbrev ℤ2ℤ : Ideal ℤ := Ideal.span {2}
abbrev ℤ3ℤ : Ideal ℤ := Ideal.span {3}

example {n : ℤ} : nℤ n = Ideal.span {n} := by
  sorry


end NZisSpan