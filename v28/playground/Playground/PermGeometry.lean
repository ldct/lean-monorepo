/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib
set_option linter.style.longLine false

/-!
*Groups: A Path to Geometry*, by R. P. Burn

Chapter 3, problems 1-5: Groups of permutations of `ℝ`
-/

open Equiv
open MulAction

/-! ## Problem 1 -/

abbrev addRight (a : ℝ) : Perm ℝ where
  toFun := fun x ↦ x + a
  invFun := fun x ↦ x - a
  left_inv x := by
    dsimp
    ring
  right_inv x := by
    dsimp
    ring

@[simp] lemma inv_addRight (a : ℝ) : (addRight a)⁻¹ = addRight (-a) := by
  ext x
  rfl

/-- An element `α` of `Perm ℝ` such that, for any two real numbers `x` and `y`, `x - y = α x - α y`,
is called a *translation* of `ℝ`. -/
def IsTranslation (α : Perm ℝ) : Prop :=
  ∀ x y : ℝ, α x - α y = x - y

/-- Show that the translations form a subgroup of `Perm ℝ`. -/
def translationSubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsTranslation α }
  mul_mem' := by
    intro α β hα hβ x y
    dsimp at *
    rw [hα, hβ]
  one_mem' := by
    intro x y
    dsimp
  inv_mem' := by
    intro α hα x y
    specialize hα (α⁻¹ x) (α⁻¹ y)
    simp_all

lemma mem_translationSubgroup_iff {α : Perm ℝ} : α ∈ translationSubgroup ↔ IsTranslation α := by rfl

notation "T" => translationSubgroup

theorem mem_translationSubgroup_iff_exists_addRight {α : Perm ℝ} : α ∈ T ↔ ∃ a : ℝ, α = addRight a := by
  constructor
  intro hα
  use α 0
  simp at hα
  ext x
  simp
  specialize hα x 0
  linarith
  intro h
  obtain ⟨a, hα⟩ := h
  intro x y
  rw [hα]
  dsimp
  ring

/-! ## For fun: Integer translations -/

def IsIntegerTranslation (α : Perm ℝ) : Prop :=
  ∃ a : ℤ, α = addRight a

def integerTranslationSubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsIntegerTranslation α }
  mul_mem' := by
    intro α β ⟨a, hα⟩ ⟨b, hβ⟩
    use a + b
    rw [hα, hβ]
    ext x
    dsimp
    push_cast
    ring
  one_mem' := by
    use 0
    ext x
    simp
  inv_mem' := by
    intro α hα
    dsimp at *
    obtain ⟨a, hα⟩ := hα
    use -a
    ext x
    rw [hα]
    simp [inv_addRight]

lemma mem_integerTranslationSubgroup_iff {α : Perm ℝ} : α ∈ integerTranslationSubgroup ↔ IsIntegerTranslation α := by rfl

example : integerTranslationSubgroup ≤ translationSubgroup := by
  intro α hα
  rw [mem_translationSubgroup_iff_exists_addRight]
  rw [mem_integerTranslationSubgroup_iff] at hα
  obtain ⟨a, hα⟩ := hα
  use a


/-! ## Problem 2 -/

abbrev halfTurn (a : ℝ) : Perm ℝ where
  toFun := fun x ↦ -x + a
  invFun := fun x ↦ -x + a
  left_inv x := by
    dsimp
    ring
  right_inv x := by
    dsimp
    ring

/-- If for some real number `a`, `α` is the element `x ↦ - x + a` of `Perm ℝ`, prove that for any
two real numbers `x`, `-(x - y) = α x - α y`. -/
example (a : ℝ) :
    let α := halfTurn a
    ∀ x y, -(x - y) = α x - α y := by
  intro α x y
  rw [show α = halfTurn a by rfl]
  dsimp
  ring

/-- Find the fixed point of `α`. -/
example (a : ℝ) :
    let α := halfTurn a
    { x | α x = x } = {a / 2} := by
  ext x
  simp
  constructor <;> intro h <;> linarith

/-- An element `α` of `Perm ℝ` which preserves absolute values of lengths is an *isometry* of `ℝ`.
-/
def IsIsometry (α : Perm ℝ) : Prop :=
  ∀ x y : ℝ, |α x - α y| = |x - y|

/-- Show that the isometries form a subgroup of `Perm ℝ`. -/
abbrev isometrySubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsIsometry α }
  mul_mem' := by
    intro α β hα hβ x y
    dsimp at *
    rw [hα, hβ]
  one_mem' := by
    intro x y
    dsimp
  inv_mem' := by
    intro α hα x y
    specialize hα (α⁻¹ x) (α⁻¹ y)
    simp_all

notation "M" => isometrySubgroup

/-- Does `M` contain the translation group of `ℝ`? -/
example : T ≤ M := by
  intro α hα x y
  exact congr(|$(hα x y)|)

/-- Does `M` contain the half-turns of `ℝ`? -/
example (a : ℝ) : halfTurn a ∈ M := by
  intro x y
  simp
  rw [abs_sub_comm]
  ring_nf

/-- If `α ∈ M` and `α 0 = 5`, what can `α 2` be? -/
example {α : Perm ℝ} (hα : α ∈ M) (h : α 0 = 5) : (α 2) ∈ ({3, 7} : Set ℝ ) := by
  specialize hα 0 2
  norm_num at hα
  rw [h] at hα
  rw [abs_eq (by norm_num)] at hα
  simp
  obtain h1 | h2 := hα
  · left
    linarith
  · right
    linarith

/-- If `α ∈ M` and `α 0 = 5`, what can `α x` be? -/
example {α : Perm ℝ} (hα : α ∈ M) (h : α 0 = 5) (x : ℝ) : α x ∈ ({5 - x, 5 + x} : Set ℝ) := by
  specialize hα 0 x
  norm_num at hα
  rw [h] at hα
  rw [abs_eq_abs] at hα
  simp
  obtain h1 | h2 := hα
  · left
    linarith
  · right
    linarith

/-- If `α ∈ M` and `α 0 = a`, prove that for all `x`, `α x = ± x + a`. -/
theorem IsIsometry.eval_of_eval_zero {α : Perm ℝ} (hα : α ∈ M) {a : ℝ} (h : α 0 = a) (x : ℝ) :
    α x ∈ ({ - x + a, x + a } : Set ℝ) := by
  specialize hα 0 x
  norm_num at hα
  rw [h] at hα
  rw [abs_eq_abs] at hα
  simp
  obtain h1 | h2 := hα
  · left
    linarith
  · right
    linarith

/- If, for given `α`, `α x = x + a` and `α y = - y + a`, prove that `|x - y| = |x + y|` and
deduce that `x` or `y` is zero. -/
theorem IsIsometry.aux {α : Perm ℝ} (hα : α ∈ M) {a x y : ℝ} (hx : α x = x + a) (hy : α y = -y + a) :
    x = 0 ∨ y = 0 := by
  specialize hα x y
  rw [hx, hy] at hα
  ring_nf at hα
  rw [abs_eq_abs] at hα
  obtain h1 | h2 := hα
  · right
    linarith
  · left
    linarith

/-- If `α ∈ M` and `α 0 = a`, prove that `α` is either a half-turn or a translation. -/
theorem IsIsometry.eq_addRight_or_eq_halfTurn {α : Perm ℝ} (hα : α ∈ M) {a : ℝ} (h : α 0 = a) :
  α = addRight a ∨ α = halfTurn a := by
  have hα0 := hα 0
  simp [h, abs_eq_abs] at hα0
  obtain h1 | h2 := hα0 1
  right
  ext x
  have : a - α x = x := by
    obtain h3 | h4 := hα0 x
    · exact h3
    have h1' : α 1 = -1 + a := by linarith
    have h4' : α x = x + a := by linarith
    obtain h' | h' := aux hα h4' h1'
    simp_all
    exfalso
    norm_num at h'
  dsimp [halfTurn]
  linarith
  left
  ext x
  have : a - α x = -x := by
    obtain h3 | h4 := hα0 x
    have h2' : α 1 = 1 + a := by linarith
    have h3' : α x = -x + a := by linarith
    obtain h' | h' := aux hα h2' h3'
    exfalso
    norm_num at h'
    simp_all
    exact h4
  dsimp [addRight]
  linarith

/-- If `α ∈ M`, prove that `α` is either a half-turn or a translation. -/
example {α : Perm ℝ} (hα : α ∈ M) : ∃ a, α = addRight a ∨ α = halfTurn a := by
  use α 0
  exact IsIsometry.eq_addRight_or_eq_halfTurn hα rfl

/-! ## Problem 3 -/

/-- Find the fixed point of `x ↦ 2 * x - 1`. -/
example :
    let α := fun (x:ℝ) ↦ 2 * x - 1
    { x | α x = x } = {1} := by
  ext x
  simp
  constructor <;> intro h <;> linarith

/-- If `α` is `x ↦ a * x + b` and `a ≠ 0, 1`, find the fixed point of `α`. -/
example (a b : ℝ) (ha' : a ≠ 1) :
    let α := fun x ↦ a * x + b
    { x | α x = x } = {- b / (a - 1)} := by
  have h1 : a - 1 ≠ 0 := by
    intro h
    apply ha'
    linarith
  ext x
  simp
  constructor <;> intro h
  have : x * (a - 1) = -b := by linarith
  apply_fun (fun x ↦ x * (a - 1))
  dsimp
  rw [this]
  field_simp [h1]
  exact mul_left_injective₀ h1
  rw [h]
  apply_fun (fun x ↦ x * (a - 1))
  dsimp
  rw [add_mul]
  field_simp [h1]
  ring
  exact mul_left_injective₀ h1

/-- If `α` is the element `x ↦ a * x + b` of `Perm ℝ` and `a ≠ 0`, compare the ratio
`(x - y) / (x - z)` with the ratio `(α x - α y) / (α x - α z)` for any three distinct real numbers
`x`, `y` and `z`. -/
example (a b : ℝ) (ha : a ≠ 0) {x y z : ℝ} (hxz : x ≠ z) :
    let α := fun x ↦ a * x + b
    (x - y) / (x - z) = (α x - α y) / (α x - α z) := by
  intro α
  rw [show α x = a * x + b by rfl]
  rw [show α y = a * y + b by rfl]
  rw [show α z = a * z + b by rfl]
  simp only [add_sub_add_right_eq_sub]
  rw [show a * x - a * y = a * (x - y) by ring]
  rw [show a * x - a * z = a * (x - z) by ring]
  have : x - z ≠ 0 := by
    intro h
    have : x = z := by linarith
    exact hxz this
  field_simp

/-- A transformation which preserves ratios of lengths on the real line is called a *similarity* of
the real line. -/
def IsSimilarity (α : Perm ℝ) : Prop :=
  ∀ {x y z : ℝ}, (x ≠ y) → (x ≠ z) → (y ≠ z) →
    (x - y) / (x - z) = (α x - α y) / (α x - α z)

#check Equiv.injective
#check Function.Injective.ne

lemma ne_iff_ne (a : Perm ℝ) {x y : ℝ} : a x ≠ a y ↔ x ≠ y := by
  constructor
  intro h h'
  apply_fun (fun x ↦ a x) at h'
  exact h h'
  intro h
  apply Function.Injective.ne
  exact Equiv.injective a
  exact h

/-- Show that the similarities form a subgroup of `Perm ℝ`. -/
abbrev similaritySubgroup : Subgroup (Perm ℝ) where
  carrier := { α | IsSimilarity α }
  mul_mem' := by
    intro α β hα hβ x y z hxy hxz hyz
    dsimp at *
    unfold IsSimilarity at *
    rw [hβ, hα]
    repeat {rw [ne_iff_ne]; assumption }
    repeat assumption
  one_mem' := by
    intro x y z hxy hxz hyz
    dsimp
  inv_mem' := by
    intro α hα x y z h1 h2 h3
    dsimp at *
    unfold IsSimilarity at *
    specialize @hα (α⁻¹ x) (α⁻¹ y) (α⁻¹ z) (by rw [ne_iff_ne]; assumption) (by rw [ne_iff_ne]; assumption) (by rw [ne_iff_ne]; assumption)
    simp_all

notation "A" => similaritySubgroup

/-- Does `A` contain all the translations of `ℝ`? -/
example : T ≤ A := by
  intro α hα x y z h1 h2 h3
  rw [mem_translationSubgroup_iff] at hα
  rw [hα, hα]

/-- Does `A` contain all the half-turns of `ℝ`? -/
example {a : ℝ} : halfTurn a ∈ A := by
  intro x y z h1 h2 h3
  simp only [coe_fn_mk, add_sub_add_right_eq_sub, sub_neg_eq_add]
  have : (x - z) ≠ 0 := by
    intro h
    have : x = z := by linarith
    exact h2 this
  have : (-x + z) ≠ 0 := by
    intro h
    have : x = z := by linarith
    exact h2 this
  field_simp
  ring

/-- If `α ∈ A`, `α 0 = 5` and `α 1 = 7`, find `α y`. -/
example {α : Perm ℝ} (h : α ∈ A) (h0 : α 0 = 5) (h1 : α 1 = 7) (y : ℝ) :
    α y = 2 * y + 5 := by
  sorry

/-- If `a ∈ A`, `α O = b` and `α 1 = a + b` with `a ≠ 0`, prove that `α y = a * y + b`. -/
theorem IsSimilarity.eq_mul_left_add_right {α : Perm ℝ} (h : α ∈ A) {a b : ℝ} (ha : a ≠ 0)
    (h0 : α 0 = b) (h1 : α 1 = a + b) (y : ℝ) : α y = a * y + b := by
  sorry

/-- Prove that all similarities of the real line take the form `x ↦ a * x + b` for some `a`, `b`
with `a ≠ 0`. -/
theorem IsSimilarity.exists_eq_mul_left_add_right {α : Perm ℝ} (h : IsSimilarity α) :
    ∃ (a b : ℝ) (ha : a ≠ 0), α = fun x ↦ a * x + b := by
  sorry

/-! ## Problem 4 -/

noncomputable abbrev mulLeftaddRight (a b : ℝ) (ha : a ≠ 0) : Perm ℝ where
  toFun := fun x ↦ a * x + b
  /- If `x' = a * x + b` and `a ≠ 0`, find `x` in terms of `x'` and deduce the inverse of the
  mapping `x ↦ a * x + b`. -/
  invFun := fun x ↦ (x - b) / a
  left_inv := by
    sorry
  right_inv := by
    sorry

theorem IsSimilarity.exists_eq_mulLeftAddRight {α : Perm ℝ} (h : IsSimilarity α) :
    ∃ (a b : ℝ) (ha : a ≠ 0), α = mulLeftaddRight a b ha := by
  sorry

/-! ## Problem 5 -/

/-- Give the algebraic form of the elements in the stabiliser of 0 in the subgroup of similiarites
of R. -/
example (α : A) : α ∈ stabilizer A (0:ℝ) ↔ ∃ (a : ℝ) (ha : a ≠ 0), α = mulLeftaddRight a 0 ha := by
  sorry
