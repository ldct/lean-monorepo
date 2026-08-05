import Mathlib

/-
https://web.ma.utexas.edu/users/vandyke/notes/250a_notes/main.pdf
-/

variable {α : Type*}

namespace Borcherds

/-
Definition 1.2 - Abstract Group
-/
class Group (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = 1

attribute [simp] Group.one_mul Group.mul_one Group.inv_mul_cancel Group.mul_inv_cancel

/- Artin, 2.2.3 -/
lemma Group.left_cancel {G} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  have := congr(a⁻¹ * $h)
  rw [← mul_assoc, ← mul_assoc] at this
  simp_all

lemma Group.mul_left_cancel_iff {G} [Group G] (a b c : G) : a * b = a * c ↔ b = c := by
  grind [Group.left_cancel]

lemma Group.right_cancel {G} [Group G] (a b c : G) (h : b * a = c * a) : b = c := by
  have := congr($h * a⁻¹)
  rw [mul_assoc, mul_assoc] at this
  simp_all

lemma Group.mul_eq_one_iff_left {G} [Group G] (a b : G) : a * b = 1 ↔ a = b⁻¹ := by
  constructor
  · intro h
    rw [show 1 = b⁻¹ * b by simp] at h
    exact right_cancel _ _ _ h
  · rintro rfl
    simp

lemma Group.mul_eq_one_iff_right {G} [Group G] (a b : G) : a * b = 1 ↔ b = a⁻¹ := by
  constructor
  · intro h
    rw [show 1 = a * a⁻¹ by simp] at h
    exact left_cancel _ _ _ h
  · rintro rfl
    simp

lemma Group.left_unique_inv' {G} [Group G] (a b c : G) (ha : b * a = 1) (hb : c * a = 1) : b = c := by
  rw [← hb] at ha
  exact Group.right_cancel _ _ _ ha

lemma Group.inv_inv {G} [Group G] (a : G) : (a⁻¹)⁻¹ = a := by
  calc
    (a⁻¹)⁻¹ = (a⁻¹)⁻¹ * 1 := by simp
    _ = (a⁻¹)⁻¹ * (a⁻¹ * a) := by simp
    _ = ((a⁻¹)⁻¹ * a⁻¹) * a := by rw [Group.mul_assoc]
    _ = 1 * a := by simp
    _ = a := by simp

lemma Group.mul_inv {G} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    calc (a * b) * (b⁻¹ * a⁻¹)
        = a * (b * (b⁻¹ * a⁻¹)) := by rw [Group.mul_assoc]
      _ = a * ((b * b⁻¹) * a⁻¹) := by rw [← Group.mul_assoc b _ _]
      _ = a * a⁻¹ := by simp
      _ = 1 := by simp
  calc (a * b)⁻¹
      = (a * b)⁻¹ * 1 := by simp
    _ = (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) := by rw [← h]
    _ = ((a * b)⁻¹ * (a * b)) * (b⁻¹ * a⁻¹) := by rw [← Group.mul_assoc]
    _ = b⁻¹ * a⁻¹ := by simp

@[simp]
lemma Group.one_inv {G} [Group G] : (1 : G)⁻¹ = 1 := by
  apply Group.left_unique_inv' 1 (1⁻¹)
  · simp only [Group.inv_mul_cancel]
  · simp


/- Definition 1.8 - Left Actions

Let G be a group and S be a set. Then a map · : G × S → S is a left action of G on S iff for all s ∈ S and all g, h ∈ G we have:
- g · (h · s) = (gh) · s
- 1 · s = s
-/
class LeftAction (G S : Type*) [Group G] [SMul G S] where
  smul_smul : ∀ s : S, ∀ g h : G,  g • (h • s) = (g * h) • s
  one_smul : ∀ s : S, (1 : G) • s = s


/-
A right action is a map · : S × G → S which satisfies the analogous properties.
-/

open scoped RightActions in
class RightAction (G S : Type*) [Group G] [HSMul Gᵐᵒᵖ S S] where
  smul_smul : ∀ s : S, ∀ g h : G,  (s <• g) <• h = (s <• (g * h))
  one_smul : ∀ s : S, s <• (1 : G) = s


/-
Definition 1.9 - G-set
-/

/-
Theorem 1.1 - A set is an abstract group iff it is a concrete group. Omitted.
-/

/-
Lemma 1.1 - If we have a left action of a group G on a set S, then we automatically have a right action and vice versa.
In particular, we write s • g = s⁻¹ • g to define a right action in terms of a given left action.
-/

instance {G S} [Group G] [SMul G S] : HSMul Gᵐᵒᵖ S S where
  hSMul := fun g s => ((MulOpposite.unop g : G)⁻¹ • s)

open scoped RightActions in
lemma right_smul_def {G S} [Group G] [SMul G S] (g : G) (s : S) :
    (s <• g : S) = g⁻¹ • s := rfl

open scoped RightActions in
example {G S} [Group G] [SMul G S] [LeftAction G S] : RightAction G S where
  smul_smul s g h := by
    simp only [right_smul_def]
    rw [LeftAction.smul_smul, Group.mul_inv]
  one_smul s := by
    rw [right_smul_def, Group.one_inv, LeftAction.one_smul]

/-
Proposition 1.2 - The four left actions of a group on itself
-/

/- The trivial action -/
@[ext]
structure TrivialAction (G : Type*) [Group G] where
  val : G

instance {G} [Group G] : Mul (TrivialAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma TrivialAction.mul_val {G} [Group G] (a b : TrivialAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [Group G] : One (TrivialAction G) where one := {val := 1}
@[simp] lemma TrivialAction.one_val {G} [Group G] : (1 : TrivialAction G).val = 1 := rfl
instance {G} [Group G] : Inv (TrivialAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma TrivialAction.inv_val {G} [Group G] (a : TrivialAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [Group G] : Group (TrivialAction G) where
  mul_assoc a b c := by ext; simp [Group.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [Group G] : SMul (TrivialAction G) G where
  smul _ s := s

@[simp] lemma TrivialAction.smul_val {G} [Group G] (g : TrivialAction G) (s : G) : (g • s) = s := rfl

instance {G} [Group G] : LeftAction (TrivialAction G) G where
  smul_smul s g h := by simp
  one_smul := by simp


/- The left multiplication action -/
@[ext]
structure LeftMultiplicationAction (G : Type*) [Group G] where
  val : G

instance {G} [Group G] : Mul (LeftMultiplicationAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma LeftMultiplicationAction.mul_val {G} [Group G] (a b : LeftMultiplicationAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [Group G] : One (LeftMultiplicationAction G) where one := {val := 1}
@[simp] lemma LeftMultiplicationAction.one_val {G} [Group G] : (1 : LeftMultiplicationAction G).val = 1 := rfl
instance {G} [Group G] : Inv (LeftMultiplicationAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma LeftMultiplicationAction.inv_val {G} [Group G] (a : LeftMultiplicationAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [Group G] : Group (LeftMultiplicationAction G) where
  mul_assoc a b c := by ext; simp [Group.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [Group G] : SMul (LeftMultiplicationAction G) G where
  smul g s := g.val * s

@[simp] lemma LeftMultiplicationAction.smul_val {G} [Group G] (g : LeftMultiplicationAction G) (s : G) : (g • s) = g.val * s := rfl

instance {G} [Group G] : LeftAction (LeftMultiplicationAction G) G where
  smul_smul s g h := by
    simp [Group.mul_assoc]
  one_smul := by simp

/- The right inverse multiplication action -/
@[ext]
structure RightInverseMultiplicationAction (G : Type*) [Group G] where
  val : G

instance {G} [Group G] : Mul (RightInverseMultiplicationAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma RightInverseMultiplicationAction.mul_val {G} [Group G] (a b : RightInverseMultiplicationAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [Group G] : One (RightInverseMultiplicationAction G) where one := {val := 1}
@[simp] lemma RightInverseMultiplicationAction.one_val {G} [Group G] : (1 : RightInverseMultiplicationAction G).val = 1 := rfl
instance {G} [Group G] : Inv (RightInverseMultiplicationAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma RightInverseMultiplicationAction.inv_val {G} [Group G] (a : RightInverseMultiplicationAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [Group G] : Group (RightInverseMultiplicationAction G) where
  mul_assoc a b c := by ext; simp [Group.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [Group G] : SMul (RightInverseMultiplicationAction G) G where
  smul g s := s * g.val⁻¹

@[simp] lemma RightInverseMultiplicationAction.smul_val {G} [Group G] (g : RightInverseMultiplicationAction G) (s : G) : (g • s) = s * g.val⁻¹ := rfl

instance {G} [Group G] : LeftAction (RightInverseMultiplicationAction G) G where
  smul_smul s g h := by
    simp [Group.mul_assoc, Group.mul_inv]
  one_smul s := by
    simp

/- The conjugation multiplication action -/
@[ext]
structure ConjAction (G : Type*) [Group G] where
  val : G

instance {G} [Group G] : Mul (ConjAction G) where mul a b := {val := a.val * b.val}
@[simp] lemma ConjAction.mul_val {G} [Group G] (a b : ConjAction G) : (a * b).val = a.val * b.val := rfl
instance {G} [Group G] : One (ConjAction G) where one := {val := 1}
@[simp] lemma ConjAction.one_val {G} [Group G] : (1 : ConjAction G).val = 1 := rfl
instance {G} [Group G] : Inv (ConjAction G) where inv a := {val := a.val⁻¹}
@[simp] lemma ConjAction.inv_val {G} [Group G] (a : ConjAction G) : (a⁻¹).val = a.val⁻¹ := rfl
instance {G} [Group G] : Group (ConjAction G) where
  mul_assoc a b c := by ext; simp [Group.mul_assoc]
  one_mul a := by ext; simp
  mul_one a := by ext; simp
  inv_mul_cancel a := by ext; simp
  mul_inv_cancel a := by ext; simp

instance {G} [Group G] : SMul (ConjAction G) G where
  smul g s := g.val * s * g.val⁻¹

@[simp] lemma ConjAction.smul_val {G} [Group G] (g : ConjAction G) (s : G) : (g • s) = g.val * s * g.val⁻¹ := rfl

instance {G} [Group G] : LeftAction (ConjAction G) G where
  smul_smul s g h := by
    simp [Group.mul_assoc, Group.mul_inv]
  one_smul s := by
    simp


/- Definition 1.4 - Group Homomorphisms -/
structure GroupHom (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  map_mul : ∀ x y : G, toFun (x * y) = toFun x * toFun y

notation:100 G " →* " H => GroupHom G H

/- Proposition 1.1 - Homomorphism preserves the identity element -/
lemma GroupHom.map_one {G H} [Group G] [Group H] (φ : GroupHom G H) : φ.toFun (1 : G) = 1 := by
  have h₁ := calc
    φ.toFun 1 * 1 = φ.toFun (1 * 1) := by simp
    _ = φ.toFun 1 * φ.toFun 1 := φ.map_mul 1 1
  have := Group.left_cancel _ _ _ h₁
  exact this.symm

/- Proposition 1.1 - Homomorphism preserves inverses -/
lemma GroupHom.map_inv {G H} [Group G] [Group H] (φ : GroupHom G H) (x : G) : φ.toFun (x⁻¹) = (φ.toFun x)⁻¹ := by
  have h₁ := calc
    1 = φ.toFun 1 := by rw [GroupHom.map_one]
    _ = φ.toFun (x * x⁻¹) := by simp
    _ = φ.toFun x * φ.toFun x⁻¹ := φ.map_mul x x⁻¹
  rw [← Group.mul_eq_one_iff_right]
  exact h₁.symm

/- Definition 1.5 - Group Isomorphisms -/
structure GroupIso (G H : Type*) [Group G] [Group H] where
  toEquiv : G ≃ H
  map_mul : ∀ x y : G, toEquiv (x * y) = toEquiv x * toEquiv y
  map_one : toEquiv (1 : G) = 1
  map_inv : ∀ x : G, toEquiv (x⁻¹) = (toEquiv x)⁻¹

notation:100 G " ≅* " H => GroupIso G H

def GroupIso.toGroupHom {G H} [Group G] [Group H] (φ : G ≅* H) : G →* H where
  toFun := φ.toEquiv.toFun
  map_mul := φ.map_mul

def GroupIso.inv {G H} [Group G] [Group H] (φ : G ≅* H) : H ≅* G where
  toEquiv := φ.toEquiv.symm
  map_mul := by
    intro y1 y2
    obtain ⟨ x1, hx1 ⟩ := φ.toEquiv.surjective y1
    obtain ⟨ x2, hx2 ⟩ := φ.toEquiv.surjective y2
    rw [← hx1]
    rw [← hx2]
    rw [← φ.map_mul]
    simp
  map_one := by
    rw [← φ.map_one]
    simp
  map_inv := by
    intro y
    obtain ⟨ x, hx ⟩ := φ.toEquiv.surjective y
    rw [← hx]
    rw [← φ.map_inv x]
    simp

/-
Upgrade `→*` to a `≃` provided the underlying function is bijective.
-/
noncomputable def GroupHom.toEquiv {G H} [Group G] [Group H] (φ : G →* H) (h : Function.Bijective φ.toFun): G ≃ H where
  toFun := φ.toFun
  invFun := Function.surjInv h.surjective
  left_inv := Function.leftInverse_surjInv h
  right_inv := Function.rightInverse_surjInv h.surjective

/-
Upgrade `→*` to a `≅*` provided the underlying function is bijective.
-/
noncomputable def GroupHom.toGroupIso {G H} [Group G] [Group H] (φ : G →* H) (h : Function.Bijective φ.toFun) : G ≅* H where
  toEquiv := φ.toEquiv h
  map_mul := φ.map_mul
  map_one := φ.map_one
  map_inv := φ.map_inv


end Borcherds
