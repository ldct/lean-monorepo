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

-- 2.1.10a
example {G : Type} [Group G] (H K : Subgroup G) : Subgroup G := {
  carrier := H.carrier ∩ K.carrier
  mul_mem' := by
    rintro x y ⟨hx, hy⟩ ⟨hx', hy'⟩
    exact ⟨H.mul_mem hx hx', K.mul_mem hy hy'⟩
  one_mem' := by
    exact ⟨H.one_mem, K.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hy⟩
    exact ⟨H.inv_mem hx, K.inv_mem hy⟩
}

-- 2.1.12 part a
example {G : Type} [Group G] (hG : IsAbelian G) (n : ℤ) : Subgroup G := {
  carrier := { a^n | a : G }
  mul_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    simp
    use a * b
    have h_weaker : ∀ m : ℕ , a ^ m * b ^ m = (a * b) ^ m := by
      intro m
      induction m with
      | zero =>
        simp
      | succ m IH =>
        rw [pow_succ (a * b), ← IH, hG a, ← mul_assoc, mul_assoc (a ^ m) _ _, mul_assoc, hG _ a]
        group
    by_cases hn : n ≥ 0
    · lift n to ℕ using hn
      have := h_weaker n
      norm_cast
      simp [this]
    · simp at hn
      obtain ⟨ m, hm ⟩ : ∃ m : ℕ, m = -n := by
        use (-n).natAbs
        grind
      obtain rfl : n = -m := by grind
      have : ∀ g : G, g ^ (-(m: ℤ)) = (g ^ m)⁻¹ := by
        intro g
        group
      simp [this]
      rw [← h_weaker m, ← mul_inv_rev, hG (b^m)]
  one_mem' := by
    use 1
    simp
  inv_mem' := by
    intro x hx
    simp at *
    obtain ⟨a, rfl⟩ := hx
    use a⁻¹
    simp
}

-- part b
example {G : Type} [Group G] (hG : IsAbelian G) (n : ℤ) : Subgroup G := {
  carrier := { a | a^n = 1 }
  mul_mem' := by
    have : ∀ x y : G, ∀ m : ℕ, (x * y)^m = x^m * y^m := by
      intro x y m
      induction m with
      | zero =>
        simp
      | succ m IH =>
        simp [pow_succ, IH]
        rw [← mul_assoc, hG _ x, ← mul_assoc, hG x]
        group

    obtain ⟨n', hn⟩ := Int.eq_nat_or_neg n
    intro a b a_1 a_2
    simp_all only [Set.mem_setOf_eq]
    cases hn with
    | inl rfl =>
      grind only [zpow_natCast, mul_one]
    | inr rfl =>
      simp_all only [zpow_neg, zpow_natCast, inv_eq_one, mul_one, inv_one]


  one_mem' := by
    simp +decide
  inv_mem' := by
    intro x a
    simp_all only [Set.mem_setOf_eq, inv_zpow', zpow_neg, inv_one]
}
