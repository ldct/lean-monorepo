import Mathlib

/-
https://web.ma.utexas.edu/users/vandyke/notes/250a_notes/main.pdf
-/

variable {α : Type*}

/-
Definition 1.2 - Abstract Group
-/
class BorcherdsGroup (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

attribute [simp] BorcherdsGroup.one_mul BorcherdsGroup.mul_one BorcherdsGroup.inv_mul_cancel BorcherdsGroup.mul_inv_cancel

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

noncomputable instance {α : Type*} [Nonempty α] : BorcherdsGroup (Permutation α) where
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

noncomputable instance : BorcherdsGroup LinearTransformation where
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv_mul_cancel L := by
    ext1; exact Function.LeftInverse.comp_eq_id (Function.leftInverse_invFun L.bijective.injective)
  mul_inv_cancel L := by
    ext1; exact Function.RightInverse.comp_eq_id (Function.rightInverse_invFun L.bijective.surjective)

/- Example: symmetries of a group respecting the group structure -/
structure Automorphism (G : Type*) [BorcherdsGroup G] where
  toFun : G → G
  bijective : Function.Bijective toFun

instance {G : Type*} [BorcherdsGroup G] : Mul (Automorphism G) where mul a b := {
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

noncomputable instance : BorcherdsGroup Translation where
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

/- Lemmas about the abstract group properties -/
lemma BorcherdsGroup.left_cancel {G} [BorcherdsGroup G] (a b c : G) (h : a * b = a * c) : b = c := by
  calc
    b = 1 * b := by simp
    _ = (a⁻¹ * a) * b := by simp
    _ = a⁻¹ * (a * b) := by rw [BorcherdsGroup.mul_assoc]
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = (a⁻¹ * a) * c := by rw [BorcherdsGroup.mul_assoc]
    _ = c := by simp

lemma BorcherdsGroup.right_cancel {G} [BorcherdsGroup G] (a b c : G) (h : b * a = c * a) : b = c := by
  calc
    b = b * 1 := by simp
    _ = b * (a * a⁻¹) := by simp
    _ = (b * a) * a⁻¹ := by rw [BorcherdsGroup.mul_assoc]
    _ = (c * a) * a⁻¹ := by rw [h]
    _ = c * (a * a⁻¹) := by rw [BorcherdsGroup.mul_assoc]
    _ = c := by simp

lemma BorcherdsGroup.mul_eq_one_iff_left {G} [BorcherdsGroup G] (a b : G) : a * b = 1 ↔ a = b⁻¹ := by
  constructor
  · intro h
    rw [show 1 = b⁻¹ * b by simp] at h
    exact right_cancel _ _ _ h
  · rintro rfl
    simp

lemma BorcherdsGroup.mul_eq_one_iff_right {G} [BorcherdsGroup G] (a b : G) : a * b = 1 ↔ b = a⁻¹ := by
  constructor
  · intro h
    rw [show 1 = a * a⁻¹ by simp] at h
    exact left_cancel _ _ _ h
  · rintro rfl
    simp

lemma BorcherdsGroup.left_unique_inv' {G} [BorcherdsGroup G] (a b c : G) (ha : b * a = 1) (hb : c * a = 1) : b = c := by
  rw [← hb] at ha
  exact BorcherdsGroup.right_cancel _ _ _ ha

lemma BorcherdsGroup.inv_inv {G} [BorcherdsGroup G] (a : G) : (a⁻¹)⁻¹ = a := by
  calc
    (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * 1 := by simp
    _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := by simp
    _ = ((a⁻¹)⁻¹ * a⁻¹) * a := by rw [BorcherdsGroup.mul_assoc]
    _ = 1 * a := by simp
    _ = a := by simp

lemma BorcherdsGroup.mul_inv {G} [BorcherdsGroup G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    calc (a * b) * (b⁻¹ * a⁻¹)
        = a * (b * (b⁻¹ * a⁻¹)) := by rw [BorcherdsGroup.mul_assoc]
      _ = a * ((b * b⁻¹) * a⁻¹) := by rw [← BorcherdsGroup.mul_assoc b _ _]
      _ = a * a⁻¹ := by simp
      _ = 1 := by simp
  calc (a * b)⁻¹
      = (a * b)⁻¹ * 1 := by simp
    _ = (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) := by rw [← h]
    _ = ((a * b)⁻¹ * (a * b)) * (b⁻¹ * a⁻¹) := by rw [← BorcherdsGroup.mul_assoc]
    _ = b⁻¹ * a⁻¹ := by simp

@[simp]
lemma BorcherdsGroup.one_inv {G} [BorcherdsGroup G] : (1 : G)⁻¹ = 1 := by
  apply BorcherdsGroup.left_unique_inv' 1 (1⁻¹)
  · simp only [BorcherdsGroup.inv_mul_cancel]
  · simp

/- Definition 1.8 - Left Actions -/
class LeftAction (G S : Type*) [BorcherdsGroup G] [SMul G S] where
  smul_smul : ∀ s : S, ∀ g h : G,  g • (h • s) = (g * h) • s
  one_smul : ∀ s : S, (1 : G) • s = s

/-
Proposition 1.2 - The four left actions of a group on itself
-/

/- The trivial action -/
@[ext]
structure TrivialAction (G : Type*) [BorcherdsGroup G] where
  val : G

instance {G} [BorcherdsGroup G] : Mul (TrivialAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma TrivialAction.mul_val {G} [BorcherdsGroup G] (a b : TrivialAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [BorcherdsGroup G] : One (TrivialAction G) where one := {val := 1}
@[simp] lemma TrivialAction.one_val {G} [BorcherdsGroup G] : (1 : TrivialAction G).val = 1 := rfl
instance {G} [BorcherdsGroup G] : Inv (TrivialAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma TrivialAction.inv_val {G} [BorcherdsGroup G] (a : TrivialAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [BorcherdsGroup G] : BorcherdsGroup (TrivialAction G) where
  mul_assoc a b c := by ext; simp [BorcherdsGroup.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [BorcherdsGroup G] : SMul (TrivialAction G) G where
  smul _ s := s

@[simp] lemma TrivialAction.smul_val {G} [BorcherdsGroup G] (g : TrivialAction G) (s : G) : (g • s) = s := rfl

instance {G} [BorcherdsGroup G] : LeftAction (TrivialAction G) G where
  smul_smul s g h := by simp
  one_smul := by simp


/- The left multiplication action -/
@[ext]
structure LeftMultiplicationAction (G : Type*) [BorcherdsGroup G] where
  val : G

instance {G} [BorcherdsGroup G] : Mul (LeftMultiplicationAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma LeftMultiplicationAction.mul_val {G} [BorcherdsGroup G] (a b : LeftMultiplicationAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [BorcherdsGroup G] : One (LeftMultiplicationAction G) where one := {val := 1}
@[simp] lemma LeftMultiplicationAction.one_val {G} [BorcherdsGroup G] : (1 : LeftMultiplicationAction G).val = 1 := rfl
instance {G} [BorcherdsGroup G] : Inv (LeftMultiplicationAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma LeftMultiplicationAction.inv_val {G} [BorcherdsGroup G] (a : LeftMultiplicationAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [BorcherdsGroup G] : BorcherdsGroup (LeftMultiplicationAction G) where
  mul_assoc a b c := by ext; simp [BorcherdsGroup.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [BorcherdsGroup G] : SMul (LeftMultiplicationAction G) G where
  smul g s := g.val * s

@[simp] lemma LeftMultiplicationAction.smul_val {G} [BorcherdsGroup G] (g : LeftMultiplicationAction G) (s : G) : (g • s) = g.val * s := rfl

instance {G} [BorcherdsGroup G] : LeftAction (LeftMultiplicationAction G) G where
  smul_smul s g h := by
    simp [BorcherdsGroup.mul_assoc]
  one_smul := by simp

/- The right inverse multiplication action -/
@[ext]
structure RightInverseMultiplicationAction (G : Type*) [BorcherdsGroup G] where
  val : G

instance {G} [BorcherdsGroup G] : Mul (RightInverseMultiplicationAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma RightInverseMultiplicationAction.mul_val {G} [BorcherdsGroup G] (a b : RightInverseMultiplicationAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [BorcherdsGroup G] : One (RightInverseMultiplicationAction G) where one := {val := 1}
@[simp] lemma RightInverseMultiplicationAction.one_val {G} [BorcherdsGroup G] : (1 : RightInverseMultiplicationAction G).val = 1 := rfl
instance {G} [BorcherdsGroup G] : Inv (RightInverseMultiplicationAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma RightInverseMultiplicationAction.inv_val {G} [BorcherdsGroup G] (a : RightInverseMultiplicationAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [BorcherdsGroup G] : BorcherdsGroup (RightInverseMultiplicationAction G) where
  mul_assoc a b c := by ext; simp [BorcherdsGroup.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [BorcherdsGroup G] : SMul (RightInverseMultiplicationAction G) G where
  smul g s := s * g.val⁻¹

@[simp] lemma RightInverseMultiplicationAction.smul_val {G} [BorcherdsGroup G] (g : RightInverseMultiplicationAction G) (s : G) : (g • s) = s * g.val⁻¹ := rfl

instance {G} [BorcherdsGroup G] : LeftAction (RightInverseMultiplicationAction G) G where
  smul_smul s g h := by
    simp [BorcherdsGroup.mul_assoc, BorcherdsGroup.mul_inv]
  one_smul s := by
    simp

/- The conjugation multiplication action -/
@[ext]
structure ConjAction (G : Type*) [BorcherdsGroup G] where
  val : G

instance {G} [BorcherdsGroup G] : Mul (ConjAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma ConjAction.mul_val {G} [BorcherdsGroup G] (a b : ConjAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [BorcherdsGroup G] : One (ConjAction G) where one := {val := 1}
@[simp] lemma ConjAction.one_val {G} [BorcherdsGroup G] : (1 : ConjAction G).val = 1 := rfl
instance {G} [BorcherdsGroup G] : Inv (ConjAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma ConjAction.inv_val {G} [BorcherdsGroup G] (a : ConjAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [BorcherdsGroup G] : BorcherdsGroup (ConjAction G) where
  mul_assoc a b c := by ext; simp [BorcherdsGroup.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [BorcherdsGroup G] : SMul (ConjAction G) G where
  smul g s := g.val * s * g.val⁻¹

@[simp] lemma ConjAction.smul_val {G} [BorcherdsGroup G] (g : ConjAction G) (s : G) : (g • s) = g.val * s * g.val⁻¹ := rfl

instance {G} [BorcherdsGroup G] : LeftAction (ConjAction G) G where
  smul_smul s g h := by
    simp [BorcherdsGroup.mul_assoc, BorcherdsGroup.mul_inv]
  one_smul s := by
    simp

/- Definition 1.4 - Group Homomorphisms -/
structure GroupHom (G H : Type*) [BorcherdsGroup G] [BorcherdsGroup H] where
  toFun : G → H
  map_mul : ∀ x y : G, toFun (x * y) = toFun x * toFun y

/- Proposition 1.1 - Homomorphism preserves the identity element -/
lemma GroupHom.map_one {G H} [BorcherdsGroup G] [BorcherdsGroup H] (φ : GroupHom G H) : φ.toFun (1 : G) = 1 := by
  have h₁ := calc
    φ.toFun 1 * 1 = φ.toFun (1 * 1) := by simp
    _ = φ.toFun 1 * φ.toFun 1 := φ.map_mul 1 1
  have := BorcherdsGroup.left_cancel _ _ _ h₁
  exact this.symm

/- Proposition 1.1 - Homomorphism preserves inverses -/
lemma GroupHome.map_inv {G H} [BorcherdsGroup G] [BorcherdsGroup H] (φ : GroupHom G H) (x : G) : φ.toFun (x⁻¹) = (φ.toFun x)⁻¹ := by
  have h₁ := calc
    1 = φ.toFun 1 := by rw [GroupHom.map_one]
    _ = φ.toFun (x * x⁻¹) := by simp
    _ = φ.toFun x * φ.toFun x⁻¹ := φ.map_mul x x⁻¹
  rw [← BorcherdsGroup.mul_eq_one_iff_right]
  exact h₁.symm

/- Definition 1.5 - Group Isomorphisms -/
structure GroupIso (G H : Type*) [BorcherdsGroup G] [BorcherdsGroup H] where
  toEquiv : G ≃ H
  map_mul : ∀ x y : G, toEquiv (x * y) = toEquiv x * toEquiv y
  map_one : toEquiv (1 : G) = 1
  map_inv : ∀ x : G, toEquiv (x⁻¹) = (toEquiv x)⁻¹

@[ext]
structure TrivialGroup : Type where
  val : Unit

instance : One TrivialGroup where one := {val := Unit.unit}
instance : Mul TrivialGroup where mul _ _ := {val := Unit.unit}
instance : Inv TrivialGroup where inv _ := {val := Unit.unit}

instance : BorcherdsGroup TrivialGroup where
  mul_assoc a b c := by ext
  one_mul a := by ext
  mul_one a := by ext
  inv_mul_cancel a := by ext
  mul_inv_cancel a := by ext

/- The `Equiv` between any group of order 1 and the trivial group -/
def trivialEquiv {G} [BorcherdsGroup G] (h : Nat.card G = 1) : G ≃ TrivialGroup where
  toFun _ := ⟨()⟩
  invFun _ := 1
  left_inv x := by
    have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h).1
    exact Subsingleton.elim _ _
  right_inv x := by ext

/- Classification of groups of order 1 -/

/- The isomorphism between any group of order 1 and the trivial group -/
def trivialIso {G} [BorcherdsGroup G] [Fintype G] (h : Nat.card G = 1) : GroupIso G TrivialGroup where
  toEquiv := trivialEquiv h
  map_mul x y := by ext
  map_one := by ext
  map_inv x := by ext

/- Definition 1.3 - Subgroups-/
structure BSubgroup (G : Type*) [BorcherdsGroup G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ x y : G, x ∈ carrier → y ∈ carrier → x * y ∈ carrier
  inv_mem : ∀ x : G, x ∈ carrier → x⁻¹ ∈ carrier

instance {G : Type*} [BorcherdsGroup G] : CoeSort (BSubgroup G) (Type _) where
  coe H := { x : G // x ∈ H.carrier }

instance {G : Type*} [BorcherdsGroup G] (H : BSubgroup G) : BorcherdsGroup H where
  mul := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, H.mul_mem a b ha hb⟩
  one := ⟨1, H.one_mem⟩
  inv := fun ⟨a, ha⟩ => ⟨a⁻¹, H.inv_mem a ha⟩
  mul_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Subtype.ext (BorcherdsGroup.mul_assoc a b c)
  one_mul := fun ⟨a, _⟩ => Subtype.ext (BorcherdsGroup.one_mul a)
  mul_one := fun ⟨a, _⟩ => Subtype.ext (BorcherdsGroup.mul_one a)
  inv_mul_cancel := fun ⟨a, _⟩ => Subtype.ext (BorcherdsGroup.inv_mul_cancel a)
  mul_inv_cancel := fun ⟨a, _⟩ => Subtype.ext (BorcherdsGroup.mul_inv_cancel a)

section GroupActingOnSetByPointwiseMultiplication
open scoped Pointwise

def leftMulEquiv {G} [Group G] (g : G) (S : Set G) : (g • S : Set G) ≃ S where
  toFun := fun x => ⟨g⁻¹ * x.1, by
    obtain ⟨s, hs, hgs⟩ := x.2
    simp only [← hgs, smul_eq_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hs⟩
  invFun := fun x => ⟨g * x.1, Set.smul_mem_smul_set x.2⟩
  left_inv := fun x => by ext; simp
  right_inv := fun x => by ext; simp

/-- Alternative: define the map `S → g • S` directly, then prove it is bijective. -/
def leftMulMap {G} [Group G] (g : G) (S : Set G) : S → (g • S : Set G) :=
  fun x => ⟨g * x.val, Set.smul_mem_smul_set x.2⟩

lemma leftMulMap_bijective {G} [Group G] (g : G) (S : Set G) : Function.Bijective (leftMulMap g S) := by
  refine ⟨?_, ?_⟩
  · -- injective
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp_all [leftMulMap]
  · -- surjective
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, hgs⟩ := hy
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [leftMulMap, Subtype.mk.injEq]
    simpa using hgs

/-- Same signature as `leftMulEquiv`, built from `leftMulMap` + bijectivity. -/
noncomputable def leftMulEquiv' {G} [Group G] (g : G) (S : Set G) : (g • S : Set G) ≃ S :=
  (Equiv.ofBijective (leftMulMap g S) (leftMulMap_bijective g S)).symm

end GroupActingOnSetByPointwiseMultiplication

instance SameLeftCoset {G} [BorcherdsGroup G] (H : BSubgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ H.carrier
  iseqv := {
    refl := by
      intro g
      simp [H.one_mem]
    symm := by
      intro a b h
      have := H.inv_mem _ h
      rw [BorcherdsGroup.mul_inv] at this
      rwa [BorcherdsGroup.inv_inv] at this
    trans := by
      intro a b c h1 h2
      have := H.mul_mem _ _ h1 h2
      rw [← BorcherdsGroup.mul_assoc] at this
      rw [show a⁻¹ * b * b⁻¹ = a⁻¹ * (b * b⁻¹) by apply
        BorcherdsGroup.mul_assoc] at this
      simp only [BorcherdsGroup.mul_inv_cancel, BorcherdsGroup.mul_one] at this
      exact this
    }

instance {G} [BorcherdsGroup G] : HasQuotient G (BSubgroup G) where
  Quotient H := Quotient (SameLeftCoset H)

section Lagrange

variable {G : Type*} [BorcherdsGroup G] (H : BSubgroup G) (g : G)

#check (⟦g⟧ = ⟦g⟧)

open scoped Pointwise in
/-- For `g : G`, left multiplication identifies `H` with the left coset of `g`. -/
def BSubgroup.leftCosetEquiv (g : G) :
      H.carrier ≃
      { x : G // ⟦x⟧ = (⟦g⟧ : G ⧸ H) }
  where
  toFun := fun ⟨h, hh⟩ =>
    ⟨g * h, Quotient.sound (by
      -- SameLeftCoset: `(g * h)⁻¹ * g ∈ H`.
      change (g * h)⁻¹ * g ∈ H.carrier
      -- apply H.inv_mem h hh
      have key : (g * h)⁻¹ * g = h⁻¹ := by
        calc (g * h)⁻¹ * g
            = (h⁻¹ * g⁻¹) * g := by rw [BorcherdsGroup.mul_inv]
          _ = h⁻¹ * (g⁻¹ * g) := by rw [BorcherdsGroup.mul_assoc]
          _ = h⁻¹ := by simp
      rw [key]
      exact H.inv_mem h hh)⟩
  invFun := fun ⟨x, hx⟩ =>
    ⟨g⁻¹ * x, by
      have hxrel : x⁻¹ * g ∈ H.carrier := Quotient.exact hx
      have key : g⁻¹ * x = (x⁻¹ * g)⁻¹ := by
        rw [BorcherdsGroup.mul_inv, BorcherdsGroup.inv_inv]
      rw [key]
      exact H.inv_mem (x⁻¹ * g) hxrel⟩
  left_inv := fun ⟨h, _⟩ => Subtype.ext (by
    calc g⁻¹ * (g * h)
        = (g⁻¹ * g) * h := by rw [BorcherdsGroup.mul_assoc]
      _ = 1 * h := by rw [BorcherdsGroup.inv_mul_cancel]
      _ = h := by rw [BorcherdsGroup.one_mul])
  right_inv := fun ⟨x, _⟩ => Subtype.ext (by
    calc g * (g⁻¹ * x)
        = (g * g⁻¹) * x := by rw [BorcherdsGroup.mul_assoc]
      _ = 1 * x := by rw [BorcherdsGroup.mul_inv_cancel]
      _ = x := by rw [BorcherdsGroup.one_mul])

open scoped Pointwise in
def BSubgroup.leftCosetEquiv' (g : G) :
      H.carrier ≃
      (g • H.carrier : Set G)
  where
  toFun := fun ⟨h, hh⟩ => ⟨g * h, ⟨h, hh, rfl⟩⟩
  invFun := fun ⟨x, hx⟩ =>
    ⟨g⁻¹ * x, by
      obtain ⟨s, hs, hgs⟩ := hx
      have : g⁻¹ * x = s := by
        rw [← hgs]
        change g⁻¹ * (g * s) = s
        rw [← BorcherdsGroup.mul_assoc, BorcherdsGroup.inv_mul_cancel,
            BorcherdsGroup.one_mul]
      rw [this]
      exact hs⟩
  left_inv := fun ⟨h, _⟩ => Subtype.ext (by
    change g⁻¹ * (g * h) = h
    rw [← BorcherdsGroup.mul_assoc, BorcherdsGroup.inv_mul_cancel,
        BorcherdsGroup.one_mul])
  right_inv := fun ⟨x, _⟩ => Subtype.ext (by
    change g * (g⁻¹ * x) = x
    rw [← BorcherdsGroup.mul_assoc, BorcherdsGroup.mul_inv_cancel,
        BorcherdsGroup.one_mul])

open scoped Pointwise in
/-- Being in the same left coset (quotient sense) is equivalent to
    membership in the pointwise smul set `g • H.carrier`. -/
lemma BSubgroup.quotient_eq_iff_mem_smul (g x : G) :
    (⟦x⟧ : G ⧸ H) = ⟦g⟧ ↔ x ∈ g • H.carrier where
  mp hx := by
    have hmem : x⁻¹ * g ∈ H.carrier := Quotient.exact hx
    refine ⟨g⁻¹ * x, ?_, ?_⟩
    · have heq : g⁻¹ * x = (x⁻¹ * g)⁻¹ := by
        rw [BorcherdsGroup.mul_inv, BorcherdsGroup.inv_inv]
      rw [heq]
      exact H.inv_mem _ hmem
    · change g * (g⁻¹ * x) = x
      rw [← BorcherdsGroup.mul_assoc, BorcherdsGroup.mul_inv_cancel,
          BorcherdsGroup.one_mul]
  mpr := by
    rintro ⟨s, hs, hgs⟩
    have hxeq : x = g * s := hgs.symm
    apply Quotient.sound
    change x⁻¹ * g ∈ H.carrier
    rw [hxeq]
    have heq : (g * s)⁻¹ * g = s⁻¹ := by
      rw [BorcherdsGroup.mul_inv, BorcherdsGroup.mul_assoc,
          BorcherdsGroup.inv_mul_cancel, BorcherdsGroup.mul_one]
    rw [heq]
    exact H.inv_mem _ hs

/-- `G` splits non-canonically as the product of coset space and subgroup carrier (Schreier-style). -/
noncomputable def BSubgroup.groupEquivQuotientProdSubtype :
    G ≃ (G ⧸ H) × { x // x ∈ H.carrier } := by
  calc G
    -- Step 1: partition G into fibers of the quotient map
      ≃ Σ C : G ⧸ H, { x // ⟦x⟧ = C } :=
        (Equiv.sigmaFiberEquiv (Quotient.mk (SameLeftCoset H))).symm
    -- Step 2: reindex: (⟦x⟧ = C) ↔ (⟦x⟧ = ⟦Quotient.out C⟧)
    _ ≃ Σ C : G ⧸ H, { x // ⟦x⟧ = (⟦Quotient.out C⟧ : G ⧸ H) } := by
        apply Equiv.sigmaCongrRight; intro C
        apply Equiv.subtypeEquivRight; intro _
        grind [H.quotient_eq_iff_mem_smul, Quotient.out_eq]
    -- Step 3: each fiber { x // ⟦x⟧ = ⟦g⟧ } ≃ H.carrier via leftCosetEquiv
    _ ≃ Σ C : G ⧸ H, H.carrier := by
        apply Equiv.sigmaCongrRight; intro C
        exact (H.leftCosetEquiv (Quotient.out C)).symm
    -- Step 4: Σ over a constant fiber ≃ product
    _ ≃ (G ⧸ H) × { x // x ∈ H.carrier } := Equiv.sigmaEquivProd _ _

/-- **Lagrange:** `|G| = |G/H| · |H|` for finite `G` (with `|H|` meant as `Nat.card` of the carrier subtype). -/
theorem BSubgroup.card_eq_card_quotient_mul_card_carrier [Finite G] :
    Nat.card G = Nat.card (G ⧸ H) * Nat.card { x // x ∈ H.carrier } := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  rw [← Nat.card_prod]
  exact Nat.card_congr (BSubgroup.groupEquivQuotientProdSubtype H)

theorem BSubgroup.card_carrier_dvd_card [Finite G] :
  Set.ncard H.carrier ∣ Nat.card G := by
  rw [BSubgroup.card_eq_card_quotient_mul_card_carrier H]
  exact dvd_mul_left _ _

end Lagrange

/-- Integers mod `n`, written multiplicatively (so the group law is addition in `ZMod n`). -/
@[ext]
structure CyclicGroup (n : ℕ) where
  val : ZMod n

instance (n : ℕ) : Mul (CyclicGroup n) where
  mul a b := ⟨(a.val + b.val)⟩

instance (n : ℕ) : One (CyclicGroup n) where
  one := ⟨0⟩

instance (n : ℕ) : Inv (CyclicGroup n) where
  inv a := ⟨-a.val⟩

@[simp] lemma CyclicGroup.mul_val {n : ℕ} (a b : CyclicGroup n) : (a * b).val = a.val + b.val :=
  rfl

@[simp] lemma CyclicGroup.one_val (n : ℕ) : (1 : CyclicGroup n).val = 0 :=
  rfl

@[simp] lemma CyclicGroup.inv_val {n : ℕ} (a : CyclicGroup n) : (a⁻¹).val = -a.val :=
  rfl

instance (n : ℕ) : BorcherdsGroup (CyclicGroup n) where
  mul_assoc a b c := by ext; simp [add_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

@[simp] lemma CyclicGroup.mk_zero_eq_one (n : ℕ) : (⟨0⟩ : CyclicGroup n) = 1 := rfl

/- Classification of groups of order 2 -/

/- The isomorphism between any group of order 2 and the cyclic group of order 2 -/
noncomputable def orderTwoIso {G} [BorcherdsGroup G] [Fintype G] (h : Nat.card G = 2) :
    GroupIso G (CyclicGroup 2) := by
  classical
  rw [Nat.card_eq_fintype_card] at h
  have hne : ∃ g : G, g ≠ 1 := by
    by_contra hall; push Not at hall
    have : Fintype.card G ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => by rw [hall a, hall b])
    omega
  let g : G := Classical.choose hne
  have hg : g ≠ 1 := Classical.choose_spec hne
  -- Every element is 1 or g
  have helem : ∀ x : G, x = 1 ∨ x = g := by
    have huniv : ({1, g} : Finset G) = Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hg), Finset.card_singleton, h])
    intro x; simpa [← huniv] using Finset.mem_univ x
  -- g * g = 1 (it can't be g, by cancellation that would give g = 1)
  have hgg : g * g = 1 := by
    rcases helem (g * g) with h | h
    · exact h
    · exfalso; exact hg (BorcherdsGroup.left_cancel g g 1 (by simp [h]))
  -- g is its own inverse
  have hginv : g⁻¹ = g := by
    exact ((BorcherdsGroup.mul_eq_one_iff_right g g).mp hgg).symm
  -- Build the isomorphism: 1 ↦ ⟨0⟩, g ↦ ⟨1⟩
  exact {
    toEquiv := {
      toFun := fun x => if x = 1 then ⟨0⟩ else ⟨1⟩
      invFun := fun y => if y.val = 0 then 1 else g
      left_inv x := by grind [helem x]
      right_inv := by
        intro ⟨y⟩
        fin_cases y <;> grind
    }
    map_mul := by
      intro x y
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl <;> rcases helem y with rfl | rfl <;>
        simp only [hg, hgg, BorcherdsGroup.one_mul, BorcherdsGroup.mul_one] <;>
        ext <;> simp [show (1 : ZMod 2) + 1 = 0 from rfl]
    map_one := by simp only [Equiv.coe_fn_mk, if_true]; rfl
    map_inv := by
      intro x
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl
      <;> simp [hginv, CyclicGroup.inv_val, CyclicGroup.ext_iff]
  }

/- Classification of groups of order 3 -/

noncomputable def orderThreeIso {G} [BorcherdsGroup G] [Fintype G] (h : Nat.card G = 3) :
    GroupIso G (CyclicGroup 3) := by
  classical
  have hcard : Fintype.card G = 3 := by rwa [Nat.card_eq_fintype_card] at h
  -- Pick a non-identity element g
  have hne : ∃ g : G, g ≠ 1 := by
    by_contra hall; push Not at hall
    have : Fintype.card G ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => by rw [hall a, hall b])
    omega
  let g : G := Classical.choose hne
  have hg : g ≠ 1 := Classical.choose_spec hne
  -- g² ≠ 1 (otherwise {1, g} is a subgroup of order 2, but 2 ∤ 3)
  have hg2 : g * g ≠ 1 := by
    intro hgg
    let H : BSubgroup G := {
      carrier := {1, g}
      one_mem := by simp
      mul_mem := fun x y hx hy => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hgg]
      inv_mem := fun x hx => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl
        · left; exact BorcherdsGroup.one_inv
        · right; exact ((BorcherdsGroup.mul_eq_one_iff_right g g).mp hgg).symm
    }
    have hdvd := H.card_carrier_dvd_card
    rw [show H.carrier = ({1, g} : Set G) from rfl, Set.ncard_pair (Ne.symm hg), h] at hdvd
    omega
  -- g² ≠ g (by cancellation that would give g = 1)
  have hg2g : g * g ≠ g := fun heq => hg (BorcherdsGroup.left_cancel g g 1 (by simp [heq]))
  -- Every element is 1, g, or g²
  have helem : ∀ x : G, x = 1 ∨ x = g ∨ x = g * g := by
    have htriple : ({1, g, g * g} : Finset G).card = Fintype.card G := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hg, Ne.symm hg2]),
          Finset.card_insert_of_notMem (by simpa using Ne.symm hg2g),
          Finset.card_singleton, hcard]
    intro x
    have : x ∈ ({1, g, g * g} : Finset G) :=
      (Finset.eq_univ_of_card _ htriple) ▸ Finset.mem_univ x
    simpa using this
  -- g³ = 1
  have hg3 : g * g * g = 1 := by
    rcases helem (g * g * g) with h | h | h
    · exact h
    · -- g³ = g ⟹ g² = 1, contradiction
      exfalso; exact hg2 (BorcherdsGroup.right_cancel g (g * g) 1 (by simp [h]))
    · -- g³ = g² ⟹ g = 1, contradiction
      exfalso; exact hg (BorcherdsGroup.left_cancel (g * g) g 1 (by
        rw [h]; simp))
  -- Inverses: g⁻¹ = g², (g²)⁻¹ = g
  have hginv : g⁻¹ = g * g := by
    have : g * (g * g) = 1 := by rw [← BorcherdsGroup.mul_assoc]; exact hg3
    exact ((BorcherdsGroup.mul_eq_one_iff_right g (g * g)).mp this).symm
  have hg2inv : (g * g)⁻¹ = g :=
    ((BorcherdsGroup.mul_eq_one_iff_right (g * g) g).mp hg3).symm
  -- Additional multiplication facts
  have hg_g2 : g * (g * g) = 1 := by rw [← BorcherdsGroup.mul_assoc]; exact hg3
  have hg2_g2 : (g * g) * (g * g) = g := by
    calc (g * g) * (g * g)
        = ((g * g) * g) * g := by rw [← BorcherdsGroup.mul_assoc]
      _ = 1 * g := by rw [hg3]
      _ = g := by simp
  -- Build the isomorphism: 1 ↦ ⟨0⟩, g ↦ ⟨1⟩, g² ↦ ⟨2⟩
  exact {
    toEquiv := {
      toFun := fun x => if x = 1 then ⟨0⟩ else if x = g then ⟨1⟩ else ⟨2⟩
      invFun := fun y => if y.val = 0 then 1 else if y.val = 1 then g else g * g
      left_inv x := by grind [helem x]
      right_inv := by intro ⟨y⟩; fin_cases y <;> grind
    }
    map_mul x y := by
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl | rfl <;> rcases helem y with rfl | rfl | rfl <;>
        simp only [BorcherdsGroup.one_mul, BorcherdsGroup.mul_one, hg3, hg_g2, hg2_g2, if_neg hg, if_neg hg2, if_neg hg2g] <;>
        ext <;> simp +decide [CyclicGroup.mul_val, CyclicGroup.one_val]
    map_one := by simp [Equiv.coe_fn_mk]
    map_inv x := by
      simp only [Equiv.coe_fn_mk]
      rcases helem x with rfl | rfl | rfl <;>
        simp only [BorcherdsGroup.one_inv, hginv, hg2inv,
          if_neg hg, if_neg hg2, if_neg hg2g] <;>
        ext <;> simp +decide [CyclicGroup.one_val]
  }

/- Classification of groups of order 4 -/

/- The Klein four-group Z/2 × Z/2 -/
abbrev Klein4 := CyclicGroup 2 × CyclicGroup 2

instance : Mul Klein4 where
  mul a b := (a.1 * b.1, a.2 * b.2)

instance : One Klein4 where
  one := (1, 1)

instance : Inv Klein4 where
  inv a := (a.1⁻¹, a.2⁻¹)

instance : BorcherdsGroup Klein4 where
  mul_assoc a b c := by ext <;> simp [BorcherdsGroup.mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp
  mul_inv_cancel a := by ext <;> simp

inductive K4 : Type
  | one
  | a
  | b
  | c
  deriving Fintype, DecidableEq

instance : Mul K4 where
  mul r s :=
    match r, s with
    | .one, s => s
    | s, .one => s
    | .a, .a => .one
    | .b, .b => .one
    | .c, .c => .one
    | .a, .b => .c
    | .b, .a => .c
    | .a, .c => .b
    | .c, .a => .b
    | .b, .c => .a
    | .c, .b => .a

instance : One K4 where
  one := .one

instance : Inv K4 where
  inv r :=
    match r with
    | .one => .one
    | .a => .a
    | .b => .b
    | .c => .c

instance : BorcherdsGroup K4 where
  mul_assoc := by decide +revert
  one_mul := by decide +revert
  mul_one := by decide +revert
  inv_mul_cancel := by decide +revert
  mul_inv_cancel := by decide +revert

/-- Every group of order 4 is isomorphic to Z/4 or to Z/2 × Z/2.
    The distinguishing invariant: does there exist an element of order > 2? -/
noncomputable def orderFourIso {G} [BorcherdsGroup G] [Fintype G] (h : Nat.card G = 4) :
    GroupIso G (CyclicGroup 4) ⊕ GroupIso G Klein4 := by
  classical
  have hcard : Fintype.card G = 4 := by rwa [Nat.card_eq_fintype_card] at h
  -- Case split: does there exist an element of order > 2?
  by_cases h4 : ∃ g : G, g ≠ 1 ∧ g * g ≠ 1
  · /-
    Z/4 case: there exists g with g ≠ 1 and g² ≠ 1.
    The elements are {1, g, g², g³} and g⁴ = 1.
    -/
    let g : G := Classical.choose h4
    have hg : g ≠ 1 := (Classical.choose_spec h4).1
    have hg2 : g * g ≠ 1 := (Classical.choose_spec h4).2
    have hg2g : g * g ≠ g := fun heq => hg (BorcherdsGroup.left_cancel g g 1 (by simp [heq]))
    -- g³ ≠ 1 (by Lagrange: {1, g, g²} would be subgroup of order 3, but 3 ∤ 4)
    have hg3 : g * g * g ≠ 1 := by
      intro hggg
      let H : BSubgroup G := {
        carrier := {1, g, g * g}
        one_mem := by simp
        mul_mem := fun x y hx hy => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
            simp -failIfUnchanged
          · left; rw [← BorcherdsGroup.mul_assoc]; exact hggg  -- g*(g²) = g³ = 1
          · left; exact hggg  -- g²*g = g³ = 1
          · -- g²*g² = g⁴ = g³*g = 1*g = g
            right; left
            calc (g * g) * (g * g)
                = ((g * g) * g) * g := by rw [← BorcherdsGroup.mul_assoc]
              _ = 1 * g := by rw [hggg]
              _ = g := by simp
        inv_mem := fun x hx => by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
          rcases hx with rfl | rfl | rfl
          · left; exact BorcherdsGroup.one_inv
          · -- g⁻¹ = g² (since g²*g = g³ = 1)
            right; right
            exact ((BorcherdsGroup.mul_eq_one_iff_left (g * g) g).mp hggg).symm
          · -- (g²)⁻¹ = g (since g²*g = g³ = 1)
            right; left
            exact ((BorcherdsGroup.mul_eq_one_iff_right (g * g) g).mp hggg).symm
      }
      have hdvd := H.card_carrier_dvd_card
      rw [show H.carrier = ({1, g, g * g} : Set G) from rfl] at hdvd
      have : Set.ncard ({1, g, g * g} : Set G) = 3 := by
        rw [show ({1, g, g * g} : Set G) = {1, g, g * g} from rfl]
        rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hg, Ne.symm hg2])]
        rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hg2g])]
        simp
      rw [this, h] at hdvd
      omega
    -- g³ ≠ g, g³ ≠ g²
    have hg3g : g * g * g ≠ g := fun heq =>
      hg2 (BorcherdsGroup.right_cancel g (g * g) 1 (by simp [heq]))
    have hg3g2 : g * g * g ≠ g * g := fun heq =>
      hg (BorcherdsGroup.left_cancel (g * g) g 1 (by rw [heq]; simp))
    -- Every element is 1, g, g², or g³
    have helem : ∀ x : G, x = 1 ∨ x = g ∨ x = g * g ∨ x = g * g * g := by
      have hquad : ({1, g, g * g, g * g * g} : Finset G).card = Fintype.card G := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hg, Ne.symm hg2, Ne.symm hg3]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hg2g, Ne.symm hg3g]),
            Finset.card_insert_of_notMem (by simpa using Ne.symm hg3g2),
            Finset.card_singleton, hcard]
      intro x
      have : x ∈ ({1, g, g * g, g * g * g} : Finset G) :=
        (Finset.eq_univ_of_card _ hquad) ▸ Finset.mem_univ x
      simpa using this
    -- g⁴ = 1
    have hg4 : g * g * g * g = 1 := by
      rcases helem (g * g * g * g) with h | h | h | h
      · exact h
      · exfalso; exact hg3 (BorcherdsGroup.right_cancel g (g * g * g) 1 (by simp [h]))
      · exfalso; exact hg2 (BorcherdsGroup.left_cancel (g * g) (g * g) 1 (by
          rw [BorcherdsGroup.mul_assoc (g * g) g g] at h; simp [h]))
      · exfalso; exact hg (BorcherdsGroup.left_cancel (g * g * g) g 1 (by simp [h]))
    -- Inverses
    have hginv : g⁻¹ = g * g * g := by
      have : g * (g * g * g) = 1 := by
        rw [← BorcherdsGroup.mul_assoc g (g * g) g, ← BorcherdsGroup.mul_assoc g g g]
        exact hg4
      exact ((BorcherdsGroup.mul_eq_one_iff_right g (g * g * g)).mp this).symm
    have hg2inv : (g * g)⁻¹ = g * g := by
      -- (g²)⁻¹ = g² since g⁴ = 1 means (g²)² = 1
      have h : (g * g) * (g * g) = 1 := by
        rw [← BorcherdsGroup.mul_assoc (g * g) g g]; exact hg4
      exact ((BorcherdsGroup.mul_eq_one_iff_right (g * g) (g * g)).mp h).symm
    have hg3inv : (g * g * g)⁻¹ = g :=
      ((BorcherdsGroup.mul_eq_one_iff_right (g * g * g) g).mp hg4).symm
    -- Multiplication facts
    have hg_g2 : g * (g * g) = g * g * g := by rw [BorcherdsGroup.mul_assoc]
    have hg_g3 : g * (g * g * g) = 1 := by
      rw [← BorcherdsGroup.mul_assoc g (g * g) g, ← BorcherdsGroup.mul_assoc g g g]; exact hg4
    have hg2_g : (g * g) * g = g * g * g := rfl
    have hg2_g2 : (g * g) * (g * g) = 1 := by
      rw [← BorcherdsGroup.mul_assoc]; exact hg4
    have hg2_g3 : (g * g) * (g * g * g) = g := by
      calc (g * g) * (g * g * g) = ((g * g) * (g * g)) * g := by rw [← BorcherdsGroup.mul_assoc]
        _ = 1 * g := by rw [hg2_g2]
        _ = g := by simp
    have hg3_g : (g * g * g) * g = 1 := hg4
    have hg3_g2 : (g * g * g) * (g * g) = g := by
      calc (g * g * g) * (g * g)
          = ((g * g * g) * g) * g := by rw [← BorcherdsGroup.mul_assoc]
        _ = 1 * g := by rw [hg4]
        _ = g := by simp
    have hg3_g3 : (g * g * g) * (g * g * g) = g * g := by
      calc (g * g * g) * (g * g * g)
          = ((g * g * g) * (g * g)) * g := by rw [← BorcherdsGroup.mul_assoc]
        _ = g * g := by rw [hg3_g2]
    -- Build Z/4 isomorphism: 1 ↦ ⟨0⟩, g ↦ ⟨1⟩, g² ↦ ⟨2⟩, g³ ↦ ⟨3⟩
    exact Sum.inl {
      toEquiv := {
        toFun := fun x =>
          if x = 1 then ⟨0⟩ else if x = g then ⟨1⟩
          else if x = g * g then ⟨2⟩ else ⟨3⟩
        invFun := fun y =>
          if y.val = 0 then 1 else if y.val = 1 then g
          else if y.val = 2 then g * g else g * g * g
        left_inv x := by grind [helem x]
        right_inv := by intro ⟨y⟩; fin_cases y <;> grind
      }
      map_mul x y := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          rcases helem y with rfl | rfl | rfl | rfl <;>
          simp only [BorcherdsGroup.one_mul, BorcherdsGroup.mul_one,
            hg_g2, hg_g3, hg2_g, hg2_g2, hg2_g3, hg3_g, hg3_g2, hg3_g3,
            if_pos rfl, if_neg hg, if_neg hg2, if_neg hg2g,
            if_neg hg3, if_neg hg3g, if_neg hg3g2] <;>
          ext <;> simp [CyclicGroup.mul_val, CyclicGroup.one_val] <;> decide
      map_one := by simp [Equiv.coe_fn_mk]
      map_inv x := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          simp only [BorcherdsGroup.one_inv, hginv, hg2inv, hg3inv,
            if_pos rfl, if_neg hg, if_neg hg2, if_neg hg3,
            if_neg hg2g, if_neg hg3g, if_neg hg3g2] <;>
          ext <;> simp [CyclicGroup.inv_val, CyclicGroup.one_val] <;> decide
    }
  · /-
    Klein four case: every non-identity element has order 2.
    -/
    push Not at h4
    -- Every non-identity element squares to 1
    have hall2 : ∀ x : G, x ≠ 1 → x * x = 1 := h4
    -- Pick two distinct non-identity elements g, a
    have hne : ∃ g : G, g ≠ 1 := by
      by_contra hall; push Not at hall
      have : Fintype.card G ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun a b => by rw [hall a, hall b])
      omega
    let g : G := Classical.choose hne
    have hg : g ≠ 1 := Classical.choose_spec hne
    have hg2 : g * g = 1 := hall2 g hg
    have hne2 : ∃ a : G, a ≠ 1 ∧ a ≠ g := by
      by_contra hall; push Not at hall
      have : Finset.univ ⊆ ({1, g} : Finset G) := by
        intro x _
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hx1 : x = 1
        · left; exact hx1
        · right; exact hall x hx1
      exact absurd (Finset.card_le_card this) (by
        rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hg),
            Finset.card_singleton, Finset.card_univ, hcard]; omega)
    let a : G := Classical.choose hne2
    have ha1 : a ≠ 1 := (Classical.choose_spec hne2).1
    have hag : a ≠ g := (Classical.choose_spec hne2).2
    have ha2 : a * a = 1 := hall2 a ha1
    -- The 4th element is a*g, distinct from 1, g, a
    have hag_ne1 : a * g ≠ 1 := by
      intro heq
      have haeq : a = g⁻¹ := (BorcherdsGroup.mul_eq_one_iff_left a g).mp heq
      have hginveq : g⁻¹ = g := ((BorcherdsGroup.mul_eq_one_iff_right g g).mp hg2).symm
      exact hag (haeq.trans hginveq)
    have hag_neg : a * g ≠ g :=
      fun heq => ha1 (BorcherdsGroup.right_cancel g a 1 (by simp [heq]))
    have hag_nea : a * g ≠ a :=
      fun heq => hg (BorcherdsGroup.left_cancel a g 1 (by simp [heq]))
    -- (a*g)² = 1
    have hag2 : (a * g) * (a * g) = 1 := hall2 (a * g) hag_ne1
    -- Every element is 1, g, a, or a*g
    have helem : ∀ x : G, x = 1 ∨ x = g ∨ x = a ∨ x = a * g := by
      have hquad : ({1, g, a, a * g} : Finset G).card = Fintype.card G := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hg, Ne.symm ha1, Ne.symm hag_ne1]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hag, Ne.symm hag_neg]),
            Finset.card_insert_of_notMem (by simpa using Ne.symm hag_nea),
            Finset.card_singleton, hcard]
      intro x
      have : x ∈ ({1, g, a, a * g} : Finset G) :=
        (Finset.eq_univ_of_card _ hquad) ▸ Finset.mem_univ x
      simpa using this
    -- Commutativity: g*a = a*g
    have hga : g * a = a * g := by
      rcases helem (g * a) with h | h | h | h
      · exfalso; exact hag (((BorcherdsGroup.mul_eq_one_iff_right g a).mp h).trans
            ((BorcherdsGroup.mul_eq_one_iff_right g g).mp hg2).symm)
      · exfalso; exact ha1 (BorcherdsGroup.left_cancel g a 1 (by simp [h]))
      · exfalso; exact hg (BorcherdsGroup.right_cancel a g 1 (by simp [h]))
      · exact h
    -- Inverses (all self-inverse)
    have hginv : g⁻¹ = g := ((BorcherdsGroup.mul_eq_one_iff_right g g).mp hg2).symm
    have hainv : a⁻¹ = a := ((BorcherdsGroup.mul_eq_one_iff_right a a).mp ha2).symm
    have haginv : (a * g)⁻¹ = a * g :=
      ((BorcherdsGroup.mul_eq_one_iff_right (a * g) (a * g)).mp hag2).symm
    -- Multiplication table
    have ha_ag : a * (a * g) = g := by rw [← BorcherdsGroup.mul_assoc]; simp [ha2]
    have hg_ag : g * (a * g) = a := by
      calc g * (a * g) = (g * a) * g := by rw [BorcherdsGroup.mul_assoc]
        _ = (a * g) * g := by rw [hga]
        _ = a * (g * g) := by rw [BorcherdsGroup.mul_assoc]
        _ = a := by simp [hg2]
    have hag_a : (a * g) * a = g := by
      rw [BorcherdsGroup.mul_assoc, hga, ← BorcherdsGroup.mul_assoc, ha2, BorcherdsGroup.one_mul]
    have hag_g : (a * g) * g = a := by
      rw [BorcherdsGroup.mul_assoc]; simp [hg2]
    -- Build Klein4 isomorphism: 1↦(1,1), g↦(⟨1⟩,1), a↦(1,⟨1⟩), ag↦(⟨1⟩,⟨1⟩)
    exact Sum.inr {
      toEquiv := {
        toFun := fun x =>
          if x = 1 then (⟨0⟩, ⟨0⟩)
          else if x = g then (⟨1⟩, ⟨0⟩)
          else if x = a then (⟨0⟩, ⟨1⟩)
          else (⟨1⟩, ⟨1⟩)
        invFun := fun p =>
          if p.1.val = 0 && p.2.val = 0 then 1
          else if p.1.val = 1 && p.2.val = 0 then g
          else if p.1.val = 0 && p.2.val = 1 then a
          else a * g
        left_inv x := by grind [helem x]
        right_inv := by intro ⟨⟨y1⟩, ⟨y2⟩⟩; fin_cases y1 <;> fin_cases y2 <;> grind
      }
      map_mul x y := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          rcases helem y with rfl | rfl | rfl | rfl <;>
          simp only [BorcherdsGroup.one_mul, BorcherdsGroup.mul_one,
            hg2, ha2, hag2, hga, ha_ag, hg_ag, hag_a, hag_g,
            if_pos rfl, if_neg hg, if_neg ha1, if_neg hag,
            if_neg hag_ne1, if_neg hag_neg, if_neg hag_nea,
            if_neg (Ne.symm hg), if_neg (Ne.symm ha1), if_neg (Ne.symm hag_ne1)] <;>
          ext <;> simp [CyclicGroup.mul_val, CyclicGroup.one_val] <;> decide
      map_one := by simp [Equiv.coe_fn_mk]
      map_inv x := by
        simp only [Equiv.coe_fn_mk]
        rcases helem x with rfl | rfl | rfl | rfl <;>
          simp only [BorcherdsGroup.one_inv, hginv, hainv, haginv,
            if_pos rfl, if_neg hg, if_neg ha1, if_neg hag_ne1] <;>
          ext <;> simp [CyclicGroup.inv_val, CyclicGroup.one_val] <;> decide
    }

noncomputable def orderFourIso' {G} [BorcherdsGroup G] [Fintype G] (h : Nat.card G = 4) :
    GroupIso G (CyclicGroup 4) ⊕ GroupIso G K4 := by
  rcases orderFourIso h with hZ4 | hK4
  · exact Sum.inl hZ4
  · -- hK4 : GroupIso G Klein4 = GroupIso G (CyclicGroup 2 × CyclicGroup 2)
    -- Compose with the inverse of the K4 ≃ Klein4 mapping
    let toK4 : CyclicGroup 2 × CyclicGroup 2 → K4 := fun p => match p with
      | (⟨0⟩, ⟨0⟩) => .one
      | (⟨1⟩, ⟨0⟩) => .a
      | (⟨0⟩, ⟨1⟩) => .b
      | (⟨1⟩, ⟨1⟩) => .c
    let fromK4 : K4 → CyclicGroup 2 × CyclicGroup 2 := fun x => match x with
      | .one => (⟨0⟩, ⟨0⟩)
      | .a => (⟨1⟩, ⟨0⟩)
      | .b => (⟨0⟩, ⟨1⟩)
      | .c => (⟨1⟩, ⟨1⟩)
    have hleft : ∀ p, fromK4 (toK4 p) = p := by
      intro ⟨⟨a⟩, ⟨b⟩⟩; fin_cases a <;> fin_cases b <;> rfl
    have hright : ∀ x, toK4 (fromK4 x) = x := by
      intro x; cases x <;> rfl
    have htoK4_mul : ∀ a b, toK4 (a * b) = toK4 a * toK4 b := by
      intro ⟨⟨a1⟩, ⟨a2⟩⟩ ⟨⟨b1⟩, ⟨b2⟩⟩
      fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;> decide
    have htoK4_one : toK4 1 = 1 := by decide
    have htoK4_inv : ∀ a, toK4 a⁻¹ = (toK4 a)⁻¹ := by
      intro ⟨⟨a1⟩, ⟨a2⟩⟩; fin_cases a1 <;> fin_cases a2 <;> decide
    let ps : CyclicGroup 2 × CyclicGroup 2 ≃ K4 := {
      toFun := toK4
      invFun := fromK4
      left_inv := hleft
      right_inv := hright
    }
    exact Sum.inr {
      toEquiv := hK4.toEquiv.trans ps
      map_mul := fun x y => by
        show toK4 (hK4.toEquiv (x * y)) = toK4 (hK4.toEquiv x) * toK4 (hK4.toEquiv y)
        rw [hK4.map_mul, htoK4_mul]
      map_one := by
        show toK4 (hK4.toEquiv 1) = 1
        rw [hK4.map_one, htoK4_one]
      map_inv := fun x => by
        show toK4 (hK4.toEquiv x⁻¹) = (toK4 (hK4.toEquiv x))⁻¹
        rw [hK4.map_inv, htoK4_inv]
    }


/- Powers of a group element -/

section Powers

variable {G : Type*} [BorcherdsGroup G]

def npow (g : G) : ℕ → G
  | 0 => 1
  | n + 1 => npow g n * g

@[simp] lemma Bnpow_zero (g : G) : npow g 0 = 1 := rfl
@[simp] lemma npow_succ (g : G) (n : ℕ) : npow g (n + 1) = npow g n * g := rfl
@[simp] lemma Bnpow_one (g : G) : npow g 1 = g := by simp [npow]

lemma Bnpow_add (g : G) (m n : ℕ) : npow g (m + n) = npow g m * npow g n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_succ, npow_succ, npow_succ, ih, BorcherdsGroup.mul_assoc]

end Powers

/- Cyclic subgroups -/

section CyclicSubgroup

variable {G : Type*} [BorcherdsGroup G]

/-- For g with gᵐ = 1 (m > 0), the set {gᵏ | k < m} is a subgroup. -/
def cyclicSubgroup (g : G) (m : ℕ) (hm : 0 < m) (hgm : npow g m = 1) : BSubgroup G where
  carrier := { x | ∃ k, k < m ∧ npow g k = x }
  one_mem := ⟨0, hm, rfl⟩
  mul_mem := by
    rintro x y ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    by_cases h : i + j < m
    · exact ⟨i + j, h, Bnpow_add g i j⟩
    · refine ⟨i + j - m, by omega, ?_⟩
      -- Goal: npow g (i+j-m) = npow g i * npow g j
      -- npow g i * npow g j = npow g (i+j) = npow g ((i+j-m)+m) = npow g (i+j-m) * npow g m
      --   = npow g (i+j-m) * 1 = npow g (i+j-m)
      have hstep1 : npow g i * npow g j = npow g (i + j) := (Bnpow_add g i j).symm
      have hstep2 : npow g (i + j) = npow g (i + j - m) * npow g m := by
        conv_lhs => rw [show i + j = (i + j - m) + m from by omega]
        exact Bnpow_add g (i + j - m) m
      rw [hstep1, hstep2, hgm, BorcherdsGroup.mul_one]
  inv_mem := by
    rintro x ⟨i, hi, rfl⟩
    by_cases h : i = 0
    · subst h; simp [BorcherdsGroup.one_inv]; exact ⟨0, hm, rfl⟩
    · refine ⟨m - i, by omega, ?_⟩
      have : npow g i * npow g (m - i) = 1 := by
        rw [← Bnpow_add, show i + (m - i) = m from by omega, hgm]
      exact (BorcherdsGroup.mul_eq_one_iff_right (npow g i) (npow g (m - i))).mp this

/-- If npow g is injective on {0,...,m-1}, the cyclic subgroup has m elements. -/
lemma ncard_cyclicSubgroup (g : G) (m : ℕ) (hm : 0 < m) (hgm : npow g m = 1)
    (hinj : ∀ i j, i < m → j < m → npow g i = npow g j → i = j) :
    Set.ncard (cyclicSubgroup g m hm hgm).carrier = m := by
  have hset : (cyclicSubgroup g m hm hgm).carrier = (npow g) '' (Finset.range m : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr (Finset.mem_range.mpr hk))
    · rintro ⟨k, hk, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      exact ⟨k, hk, rfl⟩
  rw [hset]
  have hfin : Set.Finite (Finset.range m : Set ℕ) := Finset.finite_toSet _
  have hinjOn : Set.InjOn (npow g) (Finset.range m : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    exact hinj a b ha hb hab
  rw [hinjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]

end CyclicSubgroup

/- Classification of groups of order p, p prime -/

section PrimeOrder

attribute [local instance] Classical.propDecidable

variable {G : Type*} [BorcherdsGroup G] [Fintype G]

/-- In a finite group, every element has finite order: ∃ k > 0, gᵏ = 1. -/
lemma exists_npow_eq_one (g : G) : ∃ k : ℕ, 0 < k ∧ npow g k = 1 := by
  -- By pigeonhole, npow g can't be injective on Fin (|G| + 1)
  by_contra hall
  push Not at hall
  have hall' : ∀ k : ℕ, 0 < k → npow g k ≠ 1 := fun k hk => hall k hk
  have hinj : Function.Injective (fun i : Fin (Fintype.card G + 1) => npow g i.val) := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.mk.injEq]
    simp only at hij
    by_contra hne
    -- WLOG i < j
    have hlt : i < j ∨ j < i := by omega
    rcases hlt with h | h
    · have heq : npow g (j - i) = 1 := by
        have hadd := Bnpow_add g (j - i) i
        rw [show (j - i) + i = j from by omega] at hadd
        -- hadd : npow g j = npow g (j-i) * npow g i
        -- hij : npow g i = npow g j
        -- so npow g (j-i) * npow g i = npow g i = 1 * npow g i
        exact BorcherdsGroup.right_cancel (npow g i) (npow g (j - i)) 1
          (by rw [← hadd, hij, BorcherdsGroup.one_mul])
      exact hall' (j - i) (by omega) heq
    · have heq : npow g (i - j) = 1 := by
        have hadd := Bnpow_add g (i - j) j
        rw [show (i - j) + j = i from by omega] at hadd
        exact BorcherdsGroup.right_cancel (npow g j) (npow g (i - j)) 1
          (by rw [← hadd, ← hij, BorcherdsGroup.one_mul])
      exact hall' (i - j) (by omega) heq
  have hle := Fintype.card_le_of_injective _ hinj
  simp [Fintype.card_fin] at hle

/-- The order of g: smallest positive k with gᵏ = 1. -/
noncomputable def elemOrder (g : G) : ℕ :=
  Nat.find (exists_npow_eq_one g)

lemma elemOrder_pos (g : G) : 0 < elemOrder g :=
  (Nat.find_spec (exists_npow_eq_one g)).1

lemma npow_elemOrder (g : G) : npow g (elemOrder g) = 1 :=
  (Nat.find_spec (exists_npow_eq_one g)).2

lemma elemOrder_minimal (g : G) (k : ℕ) (hk : 0 < k) (hgk : npow g k = 1) :
    elemOrder g ≤ k :=
  Nat.find_min' (exists_npow_eq_one g) ⟨hk, hgk⟩

/-- npow g is injective on {0, ..., elemOrder g - 1}. -/
lemma npow_injective_of_order (g : G) (i j : ℕ)
    (hi : i < elemOrder g) (hj : j < elemOrder g) (hij : npow g i = npow g j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have heq : npow g (j - i) = 1 := by
      have hadd := Bnpow_add g (j - i) i
      rw [show (j - i) + i = j from by omega] at hadd
      exact BorcherdsGroup.right_cancel (npow g i) (npow g (j - i)) 1
        (by rw [← hadd, hij, BorcherdsGroup.one_mul])
    have hle := elemOrder_minimal g (j - i) (by omega) heq
    omega
  · have heq : npow g (i - j) = 1 := by
      have hadd := Bnpow_add g (i - j) j
      rw [show (i - j) + j = i from by omega] at hadd
      exact BorcherdsGroup.right_cancel (npow g j) (npow g (i - j)) 1
        (by rw [← hadd, ← hij, BorcherdsGroup.one_mul])
    have hle := elemOrder_minimal g (i - j) (by omega) heq
    omega

/-- The order of g divides |G|. -/
lemma elemOrder_dvd_card (g : G) : elemOrder g ∣ Nat.card G := by
  have hm := elemOrder_pos g
  have hgm := npow_elemOrder g
  let H := cyclicSubgroup g (elemOrder g) hm hgm
  have hdvd : H.carrier.ncard ∣ Nat.card G := H.card_carrier_dvd_card
  have hcard : H.carrier.ncard = elemOrder g :=
    ncard_cyclicSubgroup g (elemOrder g) hm hgm (npow_injective_of_order g)
  rwa [hcard] at hdvd

/-- g ≠ 1 implies elemOrder g > 1. -/
lemma elemOrder_gt_one (g : G) (hg : g ≠ 1) : elemOrder g > 1 := by
  have hpos := elemOrder_pos g
  by_contra h
  push Not at h
  have heq : elemOrder g = 1 := by omega
  have : npow g (elemOrder g) = 1 := npow_elemOrder g
  rw [heq, Bnpow_one] at this
  exact hg this

/- Isomorphism from a group of prime order to `CyclicGroup p` (noncanonical generator choice). -/
noncomputable def myIso (hp : (Nat.card G).Prime) :
    GroupIso G (CyclicGroup (Nat.card G)) := by
  classical
  set p := Nat.card G with hp_def
  have hcard : Fintype.card G = p := by rw [← Nat.card_eq_fintype_card]
  -- Pick g ≠ 1
  have hne : ∃ g : G, g ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Fintype.card G ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => by rw [hall a, hall b])
    rw [hcard] at this; exact absurd hp.one_lt (by omega)
  let g : G := Classical.choose hne
  have hg : g ≠ 1 := Classical.choose_spec hne
  -- The order of g equals p (divides p, is > 1, p is prime)
  have hord : elemOrder g = p := by
    have hdvd := elemOrder_dvd_card g
    have hgt := elemOrder_gt_one g hg
    exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left (by omega)
  -- npow g : Fin p → G is injective, hence bijective
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hinj : Function.Injective (fun k : Fin p => npow g k.val) := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij; simp only [Fin.mk.injEq]
    exact npow_injective_of_order g i j (hord ▸ hi) (hord ▸ hj) hij
  have hbij : Function.Bijective (fun k : Fin p => npow g k.val) :=
    ⟨hinj, hinj.surjective_of_finite (Fintype.equivOfCardEq (by simp [hcard]))⟩
  -- npow g is periodic with period p
  have hgp : npow g p = 1 := hord ▸ npow_elemOrder g
  have npow_mul_p : ∀ k, npow g (k * p) = 1 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, Bnpow_add, ih, BorcherdsGroup.one_mul, hgp]
  have npow_mod : ∀ k, npow g k = npow g (k % p) := by
    intro k
    conv_lhs => rw [show k = k % p + (k / p) * p from by linarith [Nat.div_add_mod k p]]
    rw [Bnpow_add, npow_mul_p, BorcherdsGroup.mul_one]
  -- The discrete log: inverse of npow g on Fin p
  let f := Equiv.ofBijective (fun k : Fin p => npow g k.val) hbij
  -- Spec lemmas
  have f_apply : ∀ k : Fin p, f k = npow g k.val := fun _ => rfl
  have f_symm_spec : ∀ x : G, npow g (f.symm x).val = x :=
    fun x => f.apply_symm_apply x
  have f_symm_apply : ∀ k : Fin p, f.symm (npow g k.val) = k :=
    fun k => f.symm_apply_apply k
  -- Key: f.symm is an "additive-to-multiplicative" map
  -- f.symm(x * y) = f.symm(x) + f.symm(y) in Fin p (= ZMod p)
  have f_symm_mul : ∀ x y : G, f.symm (x * y) = f.symm x + f.symm y := by
    intro x y
    apply hinj; simp only
    -- LHS: npow g (f.symm (x * y)).val = x * y
    rw [f_symm_spec]
    -- RHS: npow g (f.symm x + f.symm y).val
    -- In Fin p (= ZMod p for p ≥ 2): (a + b).val = (a.val + b.val) % p
    rw [show (f.symm x + f.symm y).val = (((f.symm x).val + (f.symm y).val) % p) from
      Fin.val_add (f.symm x) (f.symm y)]
    rw [← npow_mod, Bnpow_add, f_symm_spec, f_symm_spec]
  haveI hNeZero : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp_pos⟩
  have fin_cast_zmod : ∀ a : Fin p, ZMod.val (a : ZMod p) = a.val :=
    fun a => by simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  have f_symm_one : f.symm 1 = 0 := by
    apply hinj; simp only
    rw [f_symm_spec, Fin.val_zero, Bnpow_zero]
  have f_symm_inv : ∀ x : G, f.symm x⁻¹ = -(f.symm x) := by
    intro x; apply hinj; simp only
    rw [f_symm_spec, Fin.val_neg' (f.symm x), ← npow_mod]
    have hk : (f.symm x).val < p := (f.symm x).isLt
    have hsum : npow g (p - (f.symm x).val) * npow g (f.symm x).val = 1 := by
      rw [← Bnpow_add, show (p - (f.symm x).val) + (f.symm x).val = p from by omega, hgp]
    exact (((BorcherdsGroup.mul_eq_one_iff_left
        (npow g (p - (f.symm x).val)) (npow g (f.symm x).val)).mp hsum).trans
      (by rw [f_symm_spec])).symm
  -- Coercion lemmas: Fin p operation cast to ZMod p
  have cast_add : ∀ a b : Fin p, ((a + b : Fin p) : ZMod p) = (a : ZMod p) + (b : ZMod p) :=
    fun a b => by simp [Fin.val_add]
  have cast_neg : ∀ a : Fin p, ((-a : Fin p) : ZMod p) = -(a : ZMod p) :=
    fun a => by simp [Fin.val_neg']
  have cast_zero : ((0 : Fin p) : ZMod p) = 0 := by simp
  -- Build GroupIso: x ↦ ⟨↑(f.symm x)⟩, inverse ⟨k⟩ ↦ npow g (ZMod.val k)
  exact (show GroupIso G (CyclicGroup p) from {
    toEquiv := {
      toFun := fun x => ⟨(f.symm x : ZMod p)⟩
      invFun := fun ⟨k⟩ => npow g (ZMod.val k)
      left_inv := fun x => by
        simp only [fin_cast_zmod]
        exact f_symm_spec x
      right_inv := fun ⟨k⟩ => by
        ext
        simp only
        have hlt : ZMod.val k < p := ZMod.val_lt k
        have h := f_symm_apply ⟨ZMod.val k, hlt⟩
        -- h : f.symm (npow g (ZMod.val k)) = ⟨ZMod.val k, hlt⟩ : Fin p
        -- Need: (f.symm (npow g (ZMod.val k)) : ZMod p) = k
        have : (f.symm (npow g (ZMod.val k)) : ZMod p) = ((⟨ZMod.val k, hlt⟩ : Fin p) : ZMod p) :=
          congr_arg (fun a : Fin p => (a : ZMod p)) h
        rw [this]
        simp
    }
    map_mul := fun x y => by
      ext
      simp only [Equiv.coe_fn_mk, CyclicGroup.mul_val]
      -- goal: (f.symm (x * y) : ZMod p) = (f.symm x : ZMod p) + (f.symm y : ZMod p)
      rw [congr_arg (fun a : Fin p => (a : ZMod p)) (f_symm_mul x y)]
      exact cast_add (f.symm x) (f.symm y)
    map_one := by
      ext
      simp only [Equiv.coe_fn_mk, CyclicGroup.one_val]
      -- goal: (f.symm 1 : ZMod p) = 0
      rw [congr_arg (fun a : Fin p => (a : ZMod p)) f_symm_one]
      exact cast_zero
    map_inv := fun x => by
      ext
      simp only [Equiv.coe_fn_mk, CyclicGroup.inv_val]
      -- goal: (f.symm x⁻¹ : ZMod p) = -(f.symm x : ZMod p)
      rw [congr_arg (fun a : Fin p => (a : ZMod p)) (f_symm_inv x)]
      exact cast_neg (f.symm x)
  })

end PrimeOrder

/-
Definition 1.12 (Product)
-/
instance {G H} [BorcherdsGroup G] [BorcherdsGroup H] : Mul (G × H) where
  mul a b := (a.1 * b.1, a.2 * b.2)

instance {G H} [BorcherdsGroup G] [BorcherdsGroup H] : One (G × H) where
  one := (1, 1)

instance {G H} [BorcherdsGroup G] [BorcherdsGroup H] : Inv (G × H) where
  inv a := (a.1⁻¹, a.2⁻¹)

instance {G H} [BorcherdsGroup G] [BorcherdsGroup H] : BorcherdsGroup (G × H) where
  mul_assoc a b c := by ext <;> simp [BorcherdsGroup.mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp [BorcherdsGroup.inv_mul_cancel]
  mul_inv_cancel a := by ext <;> simp [BorcherdsGroup.mul_inv_cancel]

/-
Example 1.8.a
-/
def productIso : GroupIso K4 (CyclicGroup 2 × CyclicGroup 2) := {
  toEquiv := {
    toFun := fun x => match x with
      | .one => (⟨0⟩, ⟨0⟩)
      | .a => (⟨1⟩, ⟨0⟩)
      | .b => (⟨0⟩, ⟨1⟩)
      | .c => (⟨1⟩, ⟨1⟩)
    invFun := fun p => match p with
      | (⟨0⟩, ⟨0⟩) => .one
      | (⟨1⟩, ⟨0⟩) => .a
      | (⟨0⟩, ⟨1⟩) => .b
      | (⟨1⟩, ⟨1⟩) => .c
    left_inv := by intro x; cases x <;> decide
    right_inv := by intro ⟨⟨a⟩, ⟨b⟩⟩; fin_cases a <;> fin_cases b <;> rfl
  }
  map_mul := by intro x y; cases x <;> cases y <;> ext <;> simp +decide
  map_one := rfl
  map_inv := by intro x; cases x <;> ext <;> simp
}

/-
Example 1.9 - omitted
-/

/-
Proposition 1.7, part 1
-/
def leftCopy {G} [BorcherdsGroup G] (H₁ H₂ : BSubgroup G) : BSubgroup (H₁ × H₂) where
  carrier := { p | p.2 = 1 }
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp

def rightCopy {G} [BorcherdsGroup G] (H₁ H₂ : BSubgroup G) : BSubgroup (H₁ × H₂) where
  carrier := { p | p.1 = 1 }
  one_mem := by simp
  mul_mem := by simp
  inv_mem := by simp

/-
Definition: a group is isomorphic to the product of two of its subgroups
-/
def IsIsomorphicToProductOfSubgroups (G) [BorcherdsGroup G] (H₁ H₂ : BSubgroup G) : Prop :=
  Nonempty (GroupIso (H₁ × H₂) G)

def s₁ : BSubgroup K4 := {
  carrier := { .one, .a }
  one_mem := by decide
  mul_mem := by decide
  inv_mem := by decide
}

def s₂ : BSubgroup K4 := {
  carrier := { .one, .b }
  one_mem := by decide
  mul_mem := by decide
  inv_mem := by decide
}

def s₃ : BSubgroup K4 := {
  carrier := { .one, .c }
  one_mem := by decide
  mul_mem := by decide
  inv_mem := by decide
}

example : IsIsomorphicToProductOfSubgroups K4 s₁ s₂ := by sorry

def HasTrivialIntersection (G) [BorcherdsGroup G] (H₁ H₂ : BSubgroup G) : Prop :=
  H₁.carrier ∩ H₂.carrier = {1}

def HasUniqueDecomposition (G) [BorcherdsGroup G] (H₁ H₂ : BSubgroup G) : Prop :=
  ∀ g : G, ∃ h₁ ∈ H₁.carrier, ∃ h₂ ∈ H₂.carrier, g = h₁ * h₂

def HasCommutingSubgroups (G) [BorcherdsGroup G] (H₁ H₂ : BSubgroup G) : Prop :=
  ∀ h₁ ∈ H₁.carrier, ∀ h₂ ∈ H₂.carrier, h₁ * h₂ = h₂ * h₁

example : HasTrivialIntersection K4 s₁ s₂ := by
  simp only [HasTrivialIntersection, s₁, s₂]
  ext x
  decide +revert

example : HasUniqueDecomposition K4 s₁ s₂ := by
  simp only [HasUniqueDecomposition, s₁, s₂]
  intro g
  fin_cases g <;> decide -- decide is a bit powerful here, it's closing existential goals of the form `∃ ...`

example : HasCommutingSubgroups K4 s₁ s₂ := by
  simp only [HasCommutingSubgroups, s₁, s₂]
  intro h₁ hh₁ h₂ hh₂
  decide +revert

/-
1.3 - Quotient Groups
-/
