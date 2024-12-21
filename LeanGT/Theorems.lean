import Mathlib

theorem centralizer_le_normalizer (G : Type) [Group G] (H : Subgroup G) : Subgroup.centralizer H ≤ Subgroup.normalizer H := by {
  intros g g_centralizes_h
  have ginv_centralizes_h : g⁻¹ ∈ Subgroup.centralizer H := by {
    exact?
  }

  have conj_by_ginv' (h : G) : h ∈ H → g⁻¹ * h * g ∈ H := by {
    intro hh
    specialize ginv_centralizes_h h
    rw [←ginv_centralizes_h]
    simp
    exact hh
    exact hh
  }
  rw [Subgroup.mem_centralizer_iff] at g_centralizes_h
  rw [Subgroup.mem_normalizer_iff]
  intros h
  constructor
  intros hh
  have rw1 := g_centralizes_h h hh
  rw [← rw1]
  group
  exact hh
  intros h'
  have spec := conj_by_ginv' (g * h * g⁻¹) h'
  group at spec
  exact spec
}

theorem neg_1_eq_n_minus_1 : ((-1 : ZMod n) = n-1) := by {
  simp only [CharP.cast_eq_zero, zero_sub]
}

example (a : ZMod n) (b : ZMod n) (h : a = b) : a.val = b.val := by
  exact congrArg ZMod.val h
