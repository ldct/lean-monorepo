import Mathlib

def IsAbelian (G) [Group G] : Prop := ∀ x y : G, x * y = y * x

-- 2.1.12 part a
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
    cases' Int.eq_nat_or_neg n with hn hn
    intro a b a_1 a_2
    simp_all only [Set.mem_setOf_eq]
    cases hn with
    | inl h =>
      subst h
      simp_all only [zpow_natCast, mul_one]
    | inr h_1 =>
      subst h_1
      simp_all only [zpow_neg, zpow_natCast, inv_eq_one, mul_one, inv_one]


  one_mem' := by
    simp +decide [ zpow_one ]
  inv_mem' := by
    intro x a
    simp_all only [Set.mem_setOf_eq, inv_zpow', zpow_neg, inv_one]
}
