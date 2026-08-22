import Playground.Artin.Chapter_2_4_defs

namespace Artin

-- exercise 2.4.1

variable {G : Type*} [Group G]

lemma pow_ofNat (g : G) (n : ℕ) : g ^ (n : ℤ) = g ^ n := by simp

lemma helper (a b : G) : (a * b = b * a) ↔ (b⁻¹ * a * b = a) := by
  constructor
  · intro h
    have := congr(b⁻¹ * $h)
    simp only [artinGroupCancel] at this
    exact this
  · intro h
    have := congr(b * $h)
    simp only [artinGroupCancel] at this
    exact this

lemma helper' (b : G) : b^5 = b * b * b * b * b := by
  simp [pow_succ]

example (a b : G) (h1 : order a = 7) (h2 : a ^ 3 * b = b * a ^ 3) : a*b = b*a := by
  have h3 : a ^ 7 = 1 := by
    rw [← h1, zpow_order_eq_one']
  have h4 : a ^ 14 = 1 := by
    have := zpow_order_eq_one a 2
    rw [h1] at this
    rw [zpow_npow_eq_pow_mul] at this
    simp_all
    exact this
  have h5 : a = (a^3)^5 := by
    rw [← pow_ofNat, ← pow_ofNat]
    rw [zpow_zpow_eq_pow_mul]
    simp
    rw [show (15 : ℤ) = 14 + 1 by lia]
    push _ ^ _
    have := zpow_ofNat a 14
    simp at this
    rw [this, h4]
    simp
  rw [helper]
  have h2 := congr(b⁻¹ * $h2 * b⁻¹)
  simp only [artinGroupCancel] at h2
  nth_rw 1 [h5]
  rw [helper']
  simp only [← Group.mul_assoc]
  rw [h2]
  have h2_assoc (c : G) : b⁻¹ * (a ^ 3 * c) = a ^ 3 * (b⁻¹ * c) := by
    rw [← Group.mul_assoc, h2, Group.mul_assoc]
  simp only [Group.mul_assoc, h2_assoc, Group.inv_mul_cancel, Group.mul_one]
  simp only [← Group.mul_assoc]
  rw [← helper']
  exact h5.symm

end Artin
