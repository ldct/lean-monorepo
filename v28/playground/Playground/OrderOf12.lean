import Mathlib

namespace OrderOf12

theorem orderOf_eq_twelve_iff {G : Type*} [Group G] (g : G) :
    orderOf g = 12 ↔ g ^ 12 = 1 ∧ g ^ 6 ≠ 1 ∧ g ^ 4 ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one g, ?_, ?_⟩
    · intro h6
      have h6' := orderOf_dvd_of_pow_eq_one h6
      rw [h] at h6'
      omega
    · intro h4
      have h4' := orderOf_dvd_of_pow_eq_one h4
      rw [h] at h4'
      omega
  · intro ⟨h12, h6, h4⟩
    have d12 := orderOf_dvd_of_pow_eq_one h12
    have nd6 : ¬ (orderOf g ∣ 6) := fun h => h6 (orderOf_dvd_iff_pow_eq_one.mp h)
    have nd4 : ¬ (orderOf g ∣ 4) := fun h => h4 (orderOf_dvd_iff_pow_eq_one.mp h)
    have pos : 0 < orderOf g := by
      rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
      exact ⟨12, by omega, h12⟩
    have hle := Nat.le_of_dvd (by omega) d12
    interval_cases (orderOf g) <;> omega

end OrderOf12
