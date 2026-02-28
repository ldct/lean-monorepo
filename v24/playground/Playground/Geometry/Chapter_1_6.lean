import Mathlib

set_option linter.style.longLine false


namespace Chapter_1_6

/-
This file formalizes the definitions, theorems and exercises from Chapter 1.6 of Dummit and Foote (page 36).
-/

-- Mathlib already has a notion of monoid homomorphism, with associated lemmas. For instance, here is exercise 1.6.1.
#check MonoidHom.map_pow

-- We construct this from scratch instead
structure GroupHomomorphism (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  map_mul : ∀ x y : G, toFun (x * y) = toFun x * toFun y

-- Example 1, the homomorphism from any group to itself
example {G} [Group G] : GroupHomomorphism G G := {
  toFun x := x
  map_mul _ _ := rfl
}

-- We pull forward some lemmas from Chapter 3.1

-- Proposition 3.1.1
lemma GroupHomomorphism.map_one {G H} [Group G] [Group H] (φ : GroupHomomorphism G H)
: φ.toFun 1 = 1 := by
  have : φ.toFun (1 * 1) = φ.toFun 1 * φ.toFun 1 := φ.map_mul 1 1
  rw [show (1 : G) * 1 = 1 by group] at this
  rwa [left_eq_mul] at this

-- Proposition 3.1.2
lemma GroupHomomorphism.map_inv {G H} [Group G] [Group H] (φ : GroupHomomorphism G H) (g : G) : φ.toFun (g⁻¹) = (φ.toFun g)⁻¹ := by
  have : φ.toFun (g⁻¹ * g) = φ.toFun 1 := by group
  rw [φ.map_mul, φ.map_one] at this
  exact eq_inv_of_mul_eq_one_left this

-- Exercise 1 part 1
lemma GroupHomomorphism.map_npow {G H} [Group G] [Group H] (φ : GroupHomomorphism G H) (n : ℕ) (g : G) : φ.toFun (g ^ n) = (φ.toFun g) ^ n := by
  induction n with
  | zero =>
    simp [GroupHomomorphism.map_one]
  | succ n IH =>
    rw [pow_succ, φ.map_mul, IH, pow_succ]

-- Exercise 1 part 2, also Proposition 3.1.3
lemma GroupHomomorphism.map_zpow {G H} [Group G] [Group H] (φ : GroupHomomorphism G H) (n : ℤ) (g : G) : φ.toFun (g ^ n) = (φ.toFun g) ^ n := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_natCast, φ.map_npow]
  | negSucc n =>
    simp
    sorry -- pow_inv

-- Exercise 1.6.2
example {G H} [Group G] [Group H] (φ : G ≃* H) (x : G) : orderOf x = orderOf (φ x) := by
  exact Eq.symm (MulEquiv.orderOf_eq φ x)

def IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

example : IsAbelian (DihedralGroup 2) := by
  unfold IsAbelian
  intro x y
  fin_cases x <;> fin_cases y <;> decide

example (n : ℕ) (hn : 2 < n) : ¬IsAbelian (DihedralGroup n) := by
  unfold IsAbelian
  push_neg
  use DihedralGroup.r 1, DihedralGroup.sr 0
  simp
  have h_neq : (n - 1 : ℕ) ≠ 1 := by

    omega
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ ZMod, Fin.ext_iff ]

-- 1.6.3 part 1
example {G H} [Group G] [Group H] (φ : G ≃* H) (hG : IsAbelian G) : IsAbelian H := by
  unfold IsAbelian at *
  intro x y
  obtain ⟨ x', rfl ⟩ := EquivLike.surjective φ x
  obtain ⟨ y', rfl ⟩ := EquivLike.surjective φ y
  rw [← MulEquiv.map_mul, hG x' y', MulEquiv.map_mul]

-- 1.6.11
example {H K} [Group H] [Group K] : H × K ≃ K × H := {
  toFun := fun (x, y) ↦ (y, x)
  invFun := fun (x, y) ↦ (y, x)
  left_inv := fun (x, y) ↦ by
    dsimp
  right_inv := fun (x, y) ↦ by
    dsimp
}

-- 1.6.12
example {A B C} [Group A] [Group B] [Group C] : (A × B) × C ≃ A × (B × C) := {
  toFun := fun ((x, y), z) ↦ (x, (y, z))
  invFun := fun (x, (y, z)) ↦ ((x, y), z)
  left_inv := fun ((x, y), z) ↦ by
    dsimp
  right_inv := fun (x, (y, z)) ↦ by
    dsimp
}

-- 1.6.13
example {G H} [Group G] [Group H] (φ : G →* H) : Subgroup H := {
  carrier := { φ g | g : G }
  mul_mem' := by
    rintro a b ⟨ a', rfl ⟩ ⟨ b', rfl ⟩
    use a' * b'
    exact MonoidHom.map_mul φ a' b'
  one_mem' := by
    use 1
    exact MonoidHom.map_one φ
  inv_mem' := by
    rintro x ⟨ x', rfl ⟩
    use x'⁻¹
    exact MonoidHom.map_inv φ x'
}

-- 1.6.14
def hom_kernel {G H} [Group G] [Group H] (φ : G →* H) : Subgroup G := {
  carrier := { g | φ g = 1 }
  mul_mem' := by
    rintro a b ha hb
    dsimp at *
    rw [MonoidHom.map_mul φ a b, ha, hb]
    group
  one_mem' := by
    dsimp
    exact MonoidHom.map_one φ
  inv_mem' := by
    intro x hx
    dsimp at *
    rw [MonoidHom.map_inv, hx]
    group
}

-- 1.6.16
def left_projection {G H} [Group G] [Group H] : G × H →* G := {
  toFun := fun (x, y) ↦ x
  map_mul' := by
    rintro a b
    dsimp
  map_one' := by
    dsimp
}

-- 1.6.16
example {G H} [Group G] [Group H] :
(hom_kernel (left_projection : G × H →* G)).carrier = { (1, h) | h : H } := by
  unfold hom_kernel left_projection
  dsimp
  ext x
  constructor
  · intro hx
    dsimp at *
    use x.2
    ext
    · simp [hx]
    · simp

  intro hx
  dsimp at *
  obtain ⟨ h, rfl ⟩ := hx
  simp

example {G} [Group G] : G ≃ G × (Equiv.Perm (Fin 1)) := {
  toFun := fun g ↦ (g, 1)
  invFun := fun (g, _) ↦ g
  left_inv := fun g ↦ by
    dsimp
  right_inv := fun (g, p) ↦ by
    dsimp
    ext x
    · dsimp
    · simp
}

-- 1.6.17 part 1
example {G} [Group G] (hG : IsAbelian G) : G →* G:= {
  toFun := fun g ↦ g⁻¹
  map_mul' := by
    rintro a b
    have : a * b = b * a := by exact hG a b
    rw [this]
    group
  map_one' := by
    group
}

-- 1.6.17 part 2
example {G} [Group G] (φ : G →* G) (hφ : ∀ g, φ g = g⁻¹) : IsAbelian G := by
  intro x y
  have := MonoidHom.map_mul φ x y
  simp [hφ] at this
  have : y * (y⁻¹ * x⁻¹) = y * (x⁻¹ * y⁻¹) := by rw [this]
  rw [show y * (y⁻¹ * x⁻¹) = (y * y⁻¹) * x⁻¹ by group] at this
  rw [show (y * y⁻¹) = 1 by group] at this
  rw [show 1 * x⁻¹ = x⁻¹ by group] at this
  have : x * x⁻¹ = x * (y * (x⁻¹ * y⁻¹)) := by
    conv =>
      lhs
      rw [this]
  rw [show x * x⁻¹ = 1 by group] at this
  have : 1 * y = x * (y * (x⁻¹ * y⁻¹)) * y := by
    rw [this]
  simp [mul_assoc] at this
  conv =>
    rhs
    rw [this]
  group

-- The kth roots of unity
example (k : ℕ) : Subgroup ℂˣ where
  carrier := {ζ | ζ ^ k = 1}
  one_mem' := by
    dsimp
    rw [one_pow]
  mul_mem':= by
    rintro a b ha hb
    dsimp at *
    rw [mul_pow, ha, hb, mul_one]
  inv_mem' := by
    intro x hx
    dsimp at *
    rw [inv_pow, hx, inv_one]


example : Subgroup ℂˣ where
  carrier := {ζ | ∃ k, ζ ^ k = 1}
  one_mem' := by
    dsimp
    use 1
    rw [one_pow]
  mul_mem':= by
    rintro a b ⟨ k, hk ⟩ ⟨ l, hl ⟩
    dsimp at *
    use k*l
    rw [mul_pow]
    conv =>
      lhs
      lhs
      rw [pow_mul, hk, one_pow]
    conv =>
      lhs
      rhs
      rw [mul_comm, pow_mul, hl, one_pow]
    rw [mul_one]
  inv_mem' := by
    rintro x ⟨ k, hk ⟩
    dsimp
    use k
    rw [inv_pow, hk, inv_one]

variable {G} [Group G] in #synth Group (MulEquiv G G)
variable {G} [Group G] in #synth Group (MulAut G)
variable {G} [Group G] in #synth Group (MulAut (MulAut G))

example {G} [Group G] : Group (MulAut G) where
  mul := fun g h ↦ MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := MulEquiv.self_trans_symm

#synth AddGroup ℚ

#check AddAut

-- 1.6.21
example (k : ℚ) (hk : k ≠ 0) : AddAut ℚ := {
  toFun := fun x ↦ k * x
  invFun := fun x ↦ k⁻¹ * x
  left_inv := fun x ↦ by
    dsimp
    field_simp [hk]
  right_inv := fun x ↦ by
    dsimp
    field_simp [hk]
  map_add' x y := by
    ring
}

-- 1.6.22 part 1/3
example {G} [Group G] (k : ℕ) (h : IsAbelian G) : G →* G := {
  toFun := fun x ↦ x^k
  map_one' := by
    rw [one_pow]
  map_mul' := by
    rintro a b
    induction k with
    | zero =>
      group
    | succ k IH =>
      rw [pow_succ, IH, h a b, ← mul_assoc]
      conv =>
        lhs
        lhs
        rw [mul_assoc]
        rhs
        rw [← pow_succ]
      rw [mul_assoc, h _ a, ← mul_assoc, ← pow_succ]
}

-- 1.6.23
example {G} [Group G] [Fintype G]
  (σ : MulAut G)
  (hσ : ∀ g : G, σ g = g ↔ g = 1)
  (hσ' : ∀ g, σ (σ g) = g)
: IsAbelian G := by
  let ω : (G → G) := fun a ↦ a⁻¹ * σ a
  have : ω.Injective := by
    intro a b h
    unfold ω at h
    have : b * (a⁻¹ * σ a) = σ b := by
      simp [h]
    rw [← mul_assoc] at this
    have : b * a⁻¹ = σ b * (σ a)⁻¹ := by
      rw [← this]
      group
    rw [← MulEquiv.map_inv, ← MulEquiv.map_mul] at this
    have : σ (b * a⁻¹) = b * a⁻¹ := (Eq.symm this)
    rw [hσ] at this
    rw [show a = 1 * a by group, ← this]
    group
  have : ω.Surjective := Finite.surjective_of_injective this
  have : ∀ g, σ g = g⁻¹ := by
    intro g
    obtain ⟨ x, rfl ⟩ := this g
    unfold ω
    simp [hσ']
  intro a b
  have eq : σ (a * b) = σ a * σ b := MulEquiv.map_mul σ a b
  simp [this] at eq
  rw [show b⁻¹ * a⁻¹ = (a * b)⁻¹ by group] at eq
  rw [show a⁻¹ * b⁻¹ = (b * a)⁻¹ by group] at eq
  have : (a * b) * (b * a)⁻¹ = 1 := by
    rw [← eq]
    group
  rw [show b * a = 1 * (b * a) by group, ← this]
  group

def perm_rep {G A} [Group G] (σ : MulAction G A) (g : G) : Equiv.Perm A := {
  toFun := fun x ↦ g • x
  invFun := fun x ↦ g⁻¹ • x
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp
}

example {G A} [Group G] (σ : MulAction G A)
: G →* Equiv.Perm A := {
  toFun := fun g ↦ perm_rep σ g
  map_one' := by
    unfold perm_rep
    ext x
    simp
  map_mul' := by
    intro x y
    unfold perm_rep
    ext a
    simp [mul_smul]
}

example {G} [Group G] : MulAction G G := {
  smul := fun x y ↦ x * y
  one_smul x := by
    simp
  mul_smul := by
    rintro x y z
    simp [mul_assoc]
}


end Chapter_1_6