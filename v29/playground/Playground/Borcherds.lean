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
    simp [BorcherdsGroup.one_inv]

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
    simp [BorcherdsGroup.one_inv]

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

/-- `G` splits non-canonically as the product of coset space and subgroup carrier (Schreier-style). -/
noncomputable def BSubgroup.groupEquivQuotientProdSubtype :
    G ≃ (G ⧸ H) × { x // x ∈ H.carrier } :=
  let π := Quotient.mk (SameLeftCoset H)
  (Equiv.sigmaFiberEquiv π).symm.trans <|
    (Equiv.sigmaCongrRight fun L : G ⧸ H =>
        (Equiv.subtypeEquivRight
        (by
        intro _
        constructor
        · exact (fun h => by exact h.trans (Quotient.out_eq L).symm)
        · exact (fun h => by exact h.trans (Quotient.out_eq L))
        )
        ).trans
          (BSubgroup.leftCosetEquiv H (Quotient.out L)).symm).trans
      (Equiv.sigmaEquivProd _ _)

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

/- Classification of groups of order p, p prime -/

/- Isomorphism from a group of prime order to `CyclicGroup p` (noncanonical generator choice). -/
noncomputable def myIso {G} [BorcherdsGroup G] [Fintype G] (hp : (Nat.card G).Prime) :
    GroupIso G (CyclicGroup (Nat.card G)) :=
  sorry
