import Mathlib

abbrev AlternatingGroup (n : ℕ) := {σ : Equiv.Perm (Fin n) // Equiv.Perm.sign σ = 1}

instance (n : ℕ) : Mul (AlternatingGroup n) := {
  mul a b := ⟨a.val * b.val, by
    rw [Equiv.Perm.sign_mul, a.prop, b.prop]
    norm_num
  ⟩
}

theorem mul_eq (n : ℕ) (a b : AlternatingGroup n) : a * b = ⟨a.val * b.val, by
  rw [Equiv.Perm.sign_mul, a.prop, b.prop]
  decide
⟩ := rfl

instance (n : ℕ) : Inv (AlternatingGroup n) := {
  inv a := ⟨a.val⁻¹, by simp [Equiv.Perm.sign_inv, a.prop]⟩
}

theorem inv_eq (n : ℕ) (a : AlternatingGroup n)
: a⁻¹ = ⟨a.val⁻¹, by simp [Equiv.Perm.sign_inv, a.prop]⟩ := rfl

instance (n : ℕ) : Group (AlternatingGroup n) where
  mul_assoc a b c := by
    simp [mul_eq]
    rfl
  one := ⟨1, by simp⟩
  one_mul a := by
    simp [mul_eq]
    rfl
  mul_one a := by
    simp [mul_eq]
    rfl
  inv_mul_cancel a := by
    simp [mul_eq, inv_eq]
    rfl
