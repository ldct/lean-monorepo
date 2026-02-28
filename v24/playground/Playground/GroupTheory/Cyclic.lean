import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Playground.Geometry.ZMul

-- prove that various groups are or are not cyclic

example : (IsAddCyclic ℤ) := ⟨ 1, by
  intro x
  use x
  simp
⟩

example : (IsAddCyclic ℤ) := ⟨ -1, by
  intro x
  use -x
  simp
⟩

theorem my_mul_div_cancel (a b : ℤ) (b_ne_0 : b ≠ 0) : (a * b) / b = a * (b / b) := by
  refine (Int.ediv_eq_iff_eq_mul_left ?_ ?_).mpr ?_
  exact b_ne_0
  exact Int.dvd_mul_left a b
  simp
  left
  have : b / b = 1 := by exact Int.ediv_self b_ne_0
  rw [this]
  simp

namespace ZMul

-- ℤ × ℤ is not cyclic
-- D&F 12c, p60
example : ¬ IsCyclic ((ZMul) × (ZMul)) := by
  rintro ⟨ g, g_surj ⟩
  obtain ⟨ e, he ⟩ := g_surj (r 0, r 1)
  simp at he
  have : g^e = (_, (r g.2.1)^e) := rfl
  rw [this] at he
  simp only [Prod.mk.injEq] at he
  obtain hg01 := he.2
  rw [rz_zpow] at hg01
  simp at hg01
  have fst_nz : g.2.1 ≠ 0 := by exact left_ne_zero_of_mul_eq_one hg01

  obtain ⟨ e, he ⟩ := g_surj (r 1, r 0)
  simp at he
  have : g^e = ((r g.1.1)^e, _) := rfl
  rw [this] at he
  simp only [Prod.mk.injEq] at he
  obtain hg01 := he.1
  rw [rz_zpow] at hg01
  simp at hg01
  have snd_nz : g.1.1 ≠ 0 := by exact left_ne_zero_of_mul_eq_one hg01

  obtain ⟨ k, hk ⟩ := g_surj (r g.1.1, r (- g.2.1))
  simp at hk

  have : g^k = ((r g.1.1)^k, (r g.2.1)^k) := rfl
  rw [this] at hk
  simp only [Prod.mk.injEq] at hk

  have := hk.left
  rw [rz_zpow] at this
  simp at this
  have k_eq_1 : k = 1 := by exact Int.eq_one_of_mul_eq_self_right snd_nz this

  have := hk.right
  rw [rz_zpow] at this
  simp at this
  have t : k = -g.2.1/g.2.1 := by exact Int.eq_ediv_of_mul_eq_right fst_nz this

  have : -g.2.1 = -1 * g.2.1 := by exact Int.neg_eq_neg_one_mul g.2.1

  rw [this] at t

  simp only [my_mul_div_cancel (-1) _ fst_nz] at t
  have : g.2.1 / g.2.1 = 1 := by exact Int.ediv_self fst_nz
  rw [this] at t
  simp at t

  rw [k_eq_1] at t
  norm_num at t
