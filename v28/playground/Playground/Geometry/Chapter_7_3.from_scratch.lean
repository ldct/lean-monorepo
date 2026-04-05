import Mathlib

/-
Quotient of a ring by a homomorphism
-/

variable {G H} [Ring G] [Ring H] (φ : G →+* H)

def HomSetoid : Setoid G := {
  r a b := φ a = φ b
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by grind
    }
}

abbrev Fibre : Type* := Quotient (HomSetoid φ)

/-
Adition on `G` lifts to addition on `Fibre φ`
-/
instance : Add (Fibre φ) := ⟨
  Quotient.lift₂
    (fun x y => Quotient.mk (HomSetoid φ) (x + y))
    (by
      intro a₁ b₁ a₂ b₂ h₁ h₂
      simp only [Quotient.eq]
      change φ (a₁ + b₁) = φ (a₂ + b₂)
      change φ a₁ = φ a₂ at h₁
      change φ b₁ = φ b₂ at h₂
      rw [φ.map_add, φ.map_add, h₁, h₂]
    )
⟩

lemma add_mk (a b : G) : Quotient.mk (HomSetoid φ) a + ⟦b⟧ = ⟦a + b⟧ := rfl

instance : Zero (Fibre φ) := ⟨ Quotient.mk (HomSetoid φ) 0 ⟩
lemma zero_eq : 0 = Quotient.mk (HomSetoid φ) 0 := rfl

instance : Neg (Fibre φ) := ⟨
  Quotient.lift (fun x => Quotient.mk (HomSetoid φ) (-x)) (by
    intro a b h
    simp only [Quotient.eq]
    change φ (-a) = φ (-b)
    change φ a = φ b at h
    rw [φ.map_neg, φ.map_neg, h]
  )
⟩
lemma neg_mk (a : G)
: -(Quotient.mk (HomSetoid φ) a) = Quotient.mk (HomSetoid φ) (-a) := rfl

/-
Multiplication on `G` lifts to multiplication on `Fibre φ`
-/
instance : Mul (Fibre φ) := ⟨
  Quotient.lift₂
    (fun x y => Quotient.mk (HomSetoid φ) (x * y))
    (by
      intro a₁ b₁ a₂ b₂ h₁ h₂
      simp only [HomSetoid, Setoid.r] at h₁ h₂
      simp only [Quotient.eq]
      change φ (a₁ * b₁) = φ (a₂ * b₂)
      rw [φ.map_mul, φ.map_mul, h₁, h₂]
    )
⟩
lemma mul_mk (a b : G) : Quotient.mk (HomSetoid φ) a * ⟦b⟧ = ⟦a * b⟧ := rfl

instance : One (Fibre φ) := ⟨ Quotient.mk (HomSetoid φ) 1 ⟩
lemma one_eq : 1 = Quotient.mk (HomSetoid φ) 1 := rfl

instance : Ring (Fibre φ) := Ring.ofMinimalAxioms
  (by
    intro a b c
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    obtain ⟨ b, rfl ⟩ := Quotient.exists_rep b
    obtain ⟨ c, rfl ⟩ := Quotient.exists_rep c
    simp only [add_mk]
    congr 1
    exact add_assoc a b c
  )
  (by
    intro a
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    simp only [zero_eq, add_mk]
    congr
    exact zero_add a
  )
  (by
    intro a
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    simp only [neg_mk, add_mk, zero_eq]
    congr
    exact neg_add_cancel a
  )
  (by
    intro a b c
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    obtain ⟨ b, rfl ⟩ := Quotient.exists_rep b
    obtain ⟨ c, rfl ⟩ := Quotient.exists_rep c
    simp only [mul_mk]
    congr 1
    exact mul_assoc a b c
  )
  (by
    intro a
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    simp only [one_eq, mul_mk]
    congr
    exact one_mul a
  )
  (by
    intro a
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    simp only [one_eq, mul_mk]
    congr
    exact MulOneClass.mul_one a
  )
  (by
    intro a b c
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    obtain ⟨ b, rfl ⟩ := Quotient.exists_rep b
    obtain ⟨ c, rfl ⟩ := Quotient.exists_rep c
    simp only [mul_mk, add_mk]
    congr
    exact left_distrib a b c
  )
  (by
    intro a b c
    obtain ⟨ a, rfl ⟩ := Quotient.exists_rep a
    obtain ⟨ b, rfl ⟩ := Quotient.exists_rep b
    obtain ⟨ c, rfl ⟩ := Quotient.exists_rep c
    simp only [mul_mk, add_mk]
    congr
    exact add_mul a b c
  )


/-
Override the Mathlib definition
-/
instance : Add (Ideal ℤ) where
  add I J := {
    carrier := { i + j | (i ∈ I) (j ∈ J) }
    add_mem' := by
      intro a b ha hb
      simp at *
      obtain ⟨ iₐ, hiₐ, jₐ, hjₐ, rfl ⟩ := ha
      obtain ⟨ i₁, hi₁, j₁, hj₁, rfl ⟩ := hb
      use (iₐ + i₁)
      simp [I.add_mem hiₐ hi₁]
      use (jₐ + j₁)
      simp [J.add_mem hjₐ hj₁]
      grind
    zero_mem' := by
      use 0
      simp [I.zero_mem, J.zero_mem]
    smul_mem' := by
      intro c x hx
      simp at *
      obtain ⟨ i, hi, j, hj, rfl ⟩ := hx
      use c * i
      have := I.smul_mem c hi
      simp_all
      clear this
      use c * j
      have := J.smul_mem c hj
      simp_all
      clear this
      grind
  }
