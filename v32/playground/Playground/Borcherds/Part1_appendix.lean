import Playground.Borcherds.Part1

namespace Borcherds

/-
Definition 1.1 - Concrete Group

We won't formalize the definition of a concrete group but we will give some examples. Our examples will always be a type

struture T where
  toFun : α → α
  ...

instance : Mul T where
  mul a b := {
    toFun := a.toFun ∘ b.toFun
    ...
  }
-/

/-
Example: symmetries of ℤ that preserve the order
-/

@[ext]
structure OrderIsoZ where
  toFun : ℤ → ℤ
  order_preserving : ∀ x y, x < y ↔ toFun x < toFun y
  bijective : Function.Bijective toFun

instance : Mul OrderIsoZ where
  mul a b := {
    toFun := a.toFun ∘ b.toFun
    order_preserving := fun x y => by grind [a.order_preserving, b.order_preserving]
    bijective := a.bijective.comp b.bijective
  }

instance : One OrderIsoZ where
  one := {
    toFun := id
    order_preserving := fun x y => by grind
    bijective := Function.bijective_id
  }

noncomputable instance : Inv OrderIsoZ where
  inv a :=
    have rinv : ∀ z, a.toFun (a.toFun.invFun z) = z :=
      Function.rightInverse_invFun a.bijective.surjective
    { toFun := a.toFun.invFun
      order_preserving := fun x y => by
        have h := a.order_preserving (a.toFun.invFun x) (a.toFun.invFun y)
        rw [rinv x, rinv y] at h
        exact h.symm
      bijective := ⟨
        (Function.rightInverse_invFun a.bijective.surjective).injective,
        Function.invFun_surjective a.bijective.injective⟩ }

/-
Example: the group of permutations of a type
-/

@[ext]
structure Permutation (α : Type*) [Nonempty α] where
  toFun : α → α
  bijective : Function.Bijective toFun

instance {α : Type*} [Nonempty α] : Mul (Permutation α) where mul a b := {
  toFun := a.toFun ∘ b.toFun,
  bijective := Function.Bijective.comp a.bijective b.bijective
}
instance {α : Type*} [Nonempty α] : One (Permutation α) where one := {
  toFun := id,
  bijective := Function.bijective_id
}

noncomputable instance {α : Type*} [Nonempty α] : Inv (Permutation α) where inv a := {
  toFun := a.toFun.invFun,
  bijective := ⟨
    (Function.rightInverse_invFun a.bijective.surjective).injective,
    Function.invFun_surjective a.bijective.injective⟩
}

noncomputable instance {α : Type*} [Nonempty α] : Borcherds.Group (Permutation α) where
  mul_assoc a b c :=
    Permutation.ext (Function.comp_assoc a.toFun b.toFun c.toFun)
  one_mul a :=
    Permutation.ext (Function.id_comp a.toFun)
  mul_one a :=
    Permutation.ext (Function.comp_id a.toFun)
  inv_mul_cancel a :=
    Permutation.ext (Function.LeftInverse.comp_eq_id (Function.leftInverse_invFun a.bijective.injective))
  mul_inv_cancel a :=
    Permutation.ext (Function.RightInverse.comp_eq_id (Function.rightInverse_invFun a.bijective.surjective))

/- Example: symmetries of ℝ³ (= (Fin 3 → ℝ)) that respect the linear structure -/

abbrev R3 := Fin 3 → ℝ

instance : Nonempty R3 :=
  ⟨fun _ => 0⟩

@[ext]
structure LinearTransformation where
  toFun : R3 → R3
  toFun_add : ∀ x y : R3, toFun (x + y) = toFun x + toFun y
  toFun_smul : ∀ (c : ℝ) (x : R3), toFun (c • x) = c • toFun x
  bijective : Function.Bijective toFun

instance : Mul LinearTransformation where
  mul L M := {
    toFun := L.toFun ∘ M.toFun
    toFun_add := fun x y => by
      simp only [Function.comp_apply, M.toFun_add, L.toFun_add]
    toFun_smul := fun c x => by simp only [Function.comp_apply, M.toFun_smul, L.toFun_smul]
    bijective := L.bijective.comp M.bijective
  }

instance : One LinearTransformation where
  one := {
    toFun := id
    toFun_add := fun _ _ => rfl
    toFun_smul := fun _ _ => rfl
    bijective := Function.bijective_id
  }

noncomputable instance : Inv LinearTransformation where
  inv L :=
    have rinv : ∀ z, L.toFun (L.toFun.invFun z) = z :=
      Function.rightInverse_invFun L.bijective.surjective
    { toFun := L.toFun.invFun
      toFun_add := fun x y => L.bijective.injective (by simp [rinv, L.toFun_add])
      toFun_smul := fun c x => L.bijective.injective (by simp [rinv, L.toFun_smul])
      bijective := ⟨(Function.rightInverse_invFun L.bijective.surjective).injective,
        Function.invFun_surjective L.bijective.injective⟩ }

noncomputable instance : Borcherds.Group LinearTransformation where
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv_mul_cancel L := by
    ext1; exact Function.LeftInverse.comp_eq_id (Function.leftInverse_invFun L.bijective.injective)
  mul_inv_cancel L := by
    ext1; exact Function.RightInverse.comp_eq_id (Function.rightInverse_invFun L.bijective.surjective)

/- Example: symmetries of a group respecting the group structure -/
structure Automorphism (G : Type*) [Borcherds.Group G] where
  toFun : G → G
  bijective : Function.Bijective toFun

instance {G : Type*} [Borcherds.Group G] : Mul (Automorphism G) where mul a b := {
  toFun := a.toFun ∘ b.toFun
  bijective := a.bijective.comp b.bijective
}

/-
Postscript:

Note that it's important to specify what struture we are preserving; for instance, ℝ³ is both a vector space and a normed space, and

structure RealIsometry where
  toFun : R3 → R3
  is_isometry : ∀ x y, ‖toFun x - toFun y‖ = ‖x - y‖

is a different group then `LinearTransformation`

Sometimes writing the group as the symmetries of a type respecting the structure is more roundabout; for e.g., it's probably easier to define `Translation` directly as data without proofs


/-
Example: translations of ℤ
-/
@[ext]
structure Translation where
  toFun : ℤ → ℤ
  is_translation : ∃ d, toFun = fun x ↦ x + d

instance : Mul Translation where
  mul a b := {
    toFun := a.toFun ∘ b.toFun
    is_translation := by
      obtain ⟨d, h1⟩ := a.is_translation
      obtain ⟨e, h2⟩ := b.is_translation
      use d + e
      grind
  }

instance : One Translation where
  one := {
    toFun := id
    is_translation := by use 0; grind
  }

noncomputable instance : Inv Translation where
  inv a := {
    toFun := fun x ↦ x + -Classical.choose a.is_translation
    is_translation := ⟨-Classical.choose a.is_translation, rfl⟩
  }

noncomputable instance : Borcherds.Group Translation where
  mul_assoc a b c :=
    Translation.ext (Function.comp_assoc a.toFun b.toFun c.toFun)
  one_mul a :=
    Translation.ext (Function.id_comp a.toFun)
  mul_one a :=
    Translation.ext (Function.comp_id a.toFun)
  inv_mul_cancel a := by
    ext x; change a⁻¹.toFun (a.toFun x) = x; dsimp only [Inv.inv]
    have := congrFun (Classical.choose_spec a.is_translation) x; omega
  mul_inv_cancel a := by
    ext x; change a.toFun (a⁻¹.toFun x) = x; dsimp only [Inv.inv]
    have := congrFun (Classical.choose_spec a.is_translation) (x + -Classical.choose a.is_translation)
    omega

structure Translation where
  val : ℤ

instance : Mul Translation where
  mul a b := {
    val := a.val + b.val
  }

In other cases, for e.g. `LinearTransformation` / `RealIsometry`, it's not obvious what data we need. It turns out `LinearTransformation` is 3x3 matrices of nonzero determinant, and `RealIsometry` is 3x3 orthogonal matrices plus a translation vector.
-/

end Borcherds
