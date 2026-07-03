import Mathlib

namespace OrderOfSix

theorem orderOf_eq_six_iff {G : Type*} [Group G] (g : G) :
    orderOf g = 6 ↔ g ^ 6 = 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 2 ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one g, ?_, ?_⟩
    · intro h3
      have h3' := orderOf_dvd_of_pow_eq_one h3
      rw [h] at h3'
      omega
    · intro h2
      have h2' := orderOf_dvd_of_pow_eq_one h2
      rw [h] at h2'
      omega
  · intro ⟨h6, h3, h2⟩
    have d6 := orderOf_dvd_of_pow_eq_one h6
    have nd3 : ¬ (orderOf g ∣ 3) := fun h => h3 (orderOf_dvd_iff_pow_eq_one.mp h)
    have nd2 : ¬ (orderOf g ∣ 2) := fun h => h2 (orderOf_dvd_iff_pow_eq_one.mp h)
    have pos : 0 < orderOf g := by
      rw [orderOf_pos_iff]
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨6, by omega, h6⟩
    have hle := Nat.le_of_dvd (by omega) d6
    interval_cases (orderOf g) <;> omega

end OrderOfSix
