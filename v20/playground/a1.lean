import Mathlib

def IsSubgroup {G : Type} [Group G] (H : Set G) : Prop := H.Nonempty ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) ∧ ∀ x ∈ H, x⁻¹ ∈ H

example {G : Type} [Group G] (H : Set G) (h : IsSubgroup H) : 1 ∈ H := by
  obtain ⟨h_nonempty, h_mul_mem, h_inv_mem⟩ := h
  let g := h_nonempty.some
  have g_inv_in_H := h_inv_mem g h_nonempty.some_mem
  have := h_mul_mem g h_nonempty.some_mem g⁻¹ g_inv_in_H
  group at this
  exact this

-- Proposition 1 (Subgroup Criterion)
example {G : Type} [Group G] (H : Set G)
: (IsSubgroup H) ↔ (H.Nonempty ∧ ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) := by
  constructor
  · intro h
    obtain ⟨h_nonempty, h_mul_mem, h_inv_mem⟩ := h
    constructor
    · exact h_nonempty
    · intro x hx y hy
      have := h_mul_mem x hx y hy
      have := h_inv_mem y hy
      exact h_mul_mem x hx y⁻¹ (h_inv_mem y hy)
  · rintro ⟨ h1, h2 ⟩

    have one_in_H : 1 ∈ H := by
      have := h2 h1.some h1.some_mem h1.some h1.some_mem
      group at this
      exact this

    have h_inv_mem : ∀ x ∈ H, x⁻¹ ∈ H := by
      intro x hx
      have := h2 1 one_in_H x hx
      simp at this
      exact this


    and_intros
    · exact h1
    intro x hx y hy
    have := h2 x hx y⁻¹ (h_inv_mem y hy)
    group at this
    exact this

    exact fun x a => h_inv_mem x a

def IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

example {G : Type} [Group G] (hG : IsAbelian G) (n : ℕ) : Subgroup G := {
  carrier := { a^n | a : G }
  mul_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    simp
    use a * b
    induction n with
    | zero =>
      simp
    | succ n IH =>
      rw [pow_succ, IH, pow_succ, pow_succ]

  one_mem' := by sorry
  inv_mem' := by sorry
}
