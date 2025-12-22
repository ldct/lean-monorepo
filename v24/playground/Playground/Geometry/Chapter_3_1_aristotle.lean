/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 16b50a00-5853-4216-ab0d-ca06c85ec874

The following was proved by Aristotle:

- example : IsKleinFour (Q ⧸ (Subgroup.center Q))
-/

import Mathlib


example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

def Group.IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

def Subgroup.IsAbelian {G} [Group G] (H : Subgroup G) : Prop := ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

-- Exercise 3; every quotient of an abelian group is abelian
set_option pp.coercions false in
example {A} [Group A] (B : Subgroup A) [B.Normal] (h1 : Group.IsAbelian A)
: Group.IsAbelian (A ⧸ B) := by
  intro x y
  obtain ⟨ a, rfl ⟩ := QuotientGroup.mk_surjective x;
  obtain ⟨ b, rfl ⟩ := QuotientGroup.mk_surjective y;
  exact congr_arg _ ( h1 a b )

-- example from mm
abbrev Q := QuaternionGroup 2

example : IsKleinFour (Q ⧸ (Subgroup.center Q)) := by
  constructor;
  · rw [ Nat.card_eq_fintype_card ];
    native_decide +revert;
  · simp +decide [ Monoid.exponent ];
    split_ifs;
    · simp +decide only [Nat.find_eq_iff];
      native_decide +revert;
    · rename_i h;
      exact h <| by haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; exact?;