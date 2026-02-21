import Mathlib

set_option linter.style.longLine false

open Polynomial

/-
The ring homomorphism from ℤ to (ZMod 2) that sends an integer to 0 if it is even and 1 if it is odd.
-/
def intToZMod2 : ℤ →+* (ZMod 2) where
  toFun := fun n => if Even n then 0 else 1
  map_one' := by norm_cast
  map_mul' x y := by
    simp
    grind
  map_zero' := by
    simp
  map_add' x y := by
    by_cases hx : Even x
    <;> by_cases hy : Even y
    <;> simp [hx, hy]
    <;> grind

example : intToZMod2 6 = 0 := by decide

/-
This defines the exact same function
-/
example : ℤ →+* (ZMod 2) where
  toFun := fun n => n
  map_one' := by norm_cast
  map_mul' x y := by norm_cast
  map_zero' := by norm_cast
  map_add' x y := by norm_cast

def evalAtZero : ℚ[X] →+* ℚ where
  toFun := fun p => p.eval 0
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp

example : evalAtZero (X ^ 2 + 4) = 4 := by
  norm_num [evalAtZero]

example (p : ℚ[X]) : p*X ∈ RingHom.ker evalAtZero := by
  simp [evalAtZero]

#check RingHom.ker evalAtZero
#check Ideal

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
      simp [HomSetoid, φ.map_add]
      change φ a₁ = φ a₂ at h₁
      change φ b₁ = φ b₂ at h₂
      congr
    )
⟩

lemma add_mk (a b : G) : Quotient.mk (HomSetoid φ) a + ⟦b⟧ = ⟦a + b⟧ := rfl

instance : Zero (Fibre φ) := ⟨ Quotient.mk (HomSetoid φ) 0 ⟩
lemma zero_eq : 0 = Quotient.mk (HomSetoid φ) 0 := rfl

instance : Neg (Fibre φ) := ⟨
  Quotient.lift (fun x => Quotient.mk (HomSetoid φ) (-x)) (by
    intro a b h
    simp [HomSetoid, φ.map_neg]
    change φ a = φ b at h
    rw [h]
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
      simp [HomSetoid, φ.map_mul]
      change φ a₁ = φ a₂ at h₁
      change φ b₁ = φ b₂ at h₂
      congr
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
# Ideals
-/

#check Ideal
#check Ideal.IsTwoSided

/-
The idea 2ℤ ⊆ ℤ
-/
example : Ideal ℤ where
  carrier := { 2 * i | i : ℤ }
  add_mem' ha hb := by
    simp at ha hb
    obtain ⟨ a, rfl ⟩ := ha
    obtain ⟨ b, rfl ⟩ := hb
    use a + b
    ring
  zero_mem' := by
    use 0
    norm_num

  -- left multiplication
  smul_mem' c d hx := by
    simp at hx
    obtain ⟨ n, rfl ⟩ := hx
    use c * n
    grind [Int.zsmul_eq_mul]

/-
# Example 1, page 243

Given a ring `R`, the ideal `⊤` is the ideal of all elements of `R`, and the ideal `⊥` is the trivial ideal {0} (containing only the zero element).

The notation comes from the lattice structure on ideals, which will be defined later.
-/

example {R} [Ring R] : (⊤ : Ideal R).carrier = Set.univ := rfl
example {R} [Ring R] : (⊥ : Ideal R).carrier = {0} := rfl

example {R} [Ring R] : Ideal R where
  carrier := ⊤
  add_mem' ha hb := by simp
  zero_mem' := by simp
  smul_mem' := by simp

example {R} [Ring R] : Ideal R where
  carrier := {0}
  add_mem' ha hb := by grind
  zero_mem' := by simp
  smul_mem' := by simp

/-
# Example 2, the ideal nℤ ⊆ ℤ
-/
def Multiples (n : ℤ) : Ideal ℤ where
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

lemma multiples_1_eq_top : Multiples 1 = ⊤ := by
  ext i
  simp [Multiples]

example : Multiples 0 = ⊥ := by
  ext i
  simp [Multiples]

example : Multiples 2 = Multiples (-2) := by
  ext i
  simp [Multiples]
  constructor
  · rintro ⟨ j, rfl ⟩
    use -j
    ring
  · rintro ⟨ j, rfl ⟩
    use -j
    ring

#synth CompleteLattice (Ideal ℤ)
#synth SemilatticeSup (Submodule (Ideal ℤ) (Ideal ℤ))

example : (Multiples 2) + (Multiples 3) = (Multiples 2) ⊔ (Multiples 3) := by rw [Submodule.add_eq_sup]
/-
Sum of ideals, via Mathlib's definition
-/
example : (Multiples 2) + (Multiples 3) = (Multiples 1) := by
  simp
  ext i
  -- By Bezout's identity, since gcd(2, 3) = 1, there exist integers x and y such that 2x + 3y = 1.
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, 2 * x + 3 * y = 1 := by
    exists 2, -1;
  have h_mul : 2 * (x * i) + 3 * (y * i) = i := by
    linear_combination' hxy * i
  -- Since $2 * (x * i) + 3 * (y * i) = i$, we have $i \in nℤ 2 ⊔ nℤ 3$.
  have h_mem : i ∈ Multiples 2 ⊔ Multiples 3 := by
    exact h_mul ▸ Submodule.add_mem_sup ( ⟨ x * i, rfl ⟩ ) ( ⟨ y * i, rfl ⟩ )
  exact iff_of_true h_mem ( by exact ⟨ i, by ring ⟩ )

example (a : Ideal ℤ) : a ⊔ a = a := by order

example (a : Ideal ℤ) : a + a = a := by
  rw [Submodule.add_eq_sup]
  order

/-
Override the Mathlib definition
-/
instance : Add (Ideal ℤ) where
  add I J := {
    carrier := { i + j | (i ∈ I.carrier) (j ∈ J.carrier) }
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

lemma mem_ideal (I : Ideal ℤ) (x : ℤ)
: x ∈ I ↔ x ∈ I.carrier := by rfl

lemma ideal_carrier_ext (I J : Ideal ℤ)
: I.carrier = J.carrier ↔ I = J := by simp

lemma add_carrier_eq (I J : Ideal ℤ)
: (I + J).carrier = { i + j | (i ∈ I.carrier) (j ∈ J.carrier) } := rfl

lemma add_mem_iff' (I J : Ideal ℤ) (x : ℤ) (hx : x ∈ (I + J))
: ∃ i j, i ∈ I.carrier ∧ j ∈ J.carrier ∧ i + j = x := by
  simp
  rw [mem_ideal, add_carrier_eq] at hx
  simp at hx
  grind

lemma add_mem_iff (I J : Ideal ℤ) (x : ℤ)
: x ∈ (I + J) ↔ ∃ i j, i ∈ I.carrier ∧ j ∈ J.carrier ∧ i + j = x := by
  constructor
  · intro h
    obtain ⟨ i, j, hi, hj, rfl ⟩ := add_mem_iff' I J x h
    grind
  intro h
  obtain ⟨ i, j, hi, hj, _ ⟩ := h
  use i, hi, j, hj


example : (Multiples 2) + (Multiples 3) = (Multiples 1) := by
  simp [multiples_1_eq_top]
  ext x
  constructor
  · intro h
    exact trivial
  intro h1
  have := Int.gcd_eq_gcd_ab 2 3
  norm_num at this
  have := congr(x * $this)
  norm_num at this
  symm at this
  rw [mul_add] at this
  rw [add_mem_iff]

  use 2 * x * Int.gcdA 2 3
  simp [Multiples]
  have l : ∃ i, 2 * i = 2 * x * Int.gcdA 2 3 := by
    use x * Int.gcdA 2 3
    grind
  simp [l]
  clear l
  use x * Int.gcdB 2 3
  grind

#check Submodule.mul

#synth AddCommMagma (Ideal ℤ)


#synth SupSet (Ideal ℤ)

#check (Multiples 2) + (Multiples 2)

-- example : (ℤ ⧸ nℤ 2) ≃+* (ZMod 2) where
--   toFun := sorry
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry
--   map_add' := sorry
--   map_mul' := sorry

#synth Mul (Ideal ℤ)
#synth Ring (ℤ ⧸ Multiples 2)

#synth Ring (ℤ × ℤ )

/-
https://math.bu.edu/people/rpollack/Teach/542spring07/542hw5_solns.pdf
-/

-- 1c
example : (ℚ × ℚ) →+* ℚ where
  toFun := fun (x, y) => x
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp

-- 1d
example : (ℝ → ℝ) →+* ℝ where
  toFun := fun f => f 1
  map_one' := by
    simp
  map_mul' x y := by
    simp
  map_zero' := by
    simp
  map_add' x y := by
    simp

-- 1f
example : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := fun z => !![z.re, z.im; -z.im, z.re]
  map_one' := by
    simp [Matrix.one_fin_two]
  map_mul' x y := by
    rw [Matrix.mul_fin_two]
    congr
    <;> rw [← Complex.re_add_im x, ← Complex.re_add_im y] <;> simp <;> norm_cast
    ring
  map_zero' := by
    simp [Matrix.eta_fin_two 0]
  map_add' x y := by
    simp
    norm_cast
    ring

-- 23
example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (a, b), map_one' := by simp, map_mul' x y := by simp ; rfl, map_zero' := by simp, map_add' x y := by simp ; rfl
}

example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (b, a), map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (b, 0), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (0, b), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (a, 0), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (0, a), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →ₙ+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (0, 0), map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (a, a), map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}

example : (ℤ × ℤ) →+* (ℤ × ℤ) := {
  toFun := fun (a, b) => (b, b), map_one' := by simp, map_mul' x y := by simp, map_zero' := by simp, map_add' x y := by simp
}
