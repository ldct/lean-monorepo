import Playground.Artin.SqrtRing

open IntermediateField Real

noncomputable abbrev γ : ℝ := √2 + √3

lemma sqrt_six_eq : √6 = √2 * √3 := by
  sqrt_ring

lemma two_sqrt_six_eq : 2 * √6 = (√2 + √3) ^ 2 - 5 := by
  sqrt_ring

theorem five_add_sqrt_six_mem :  √6 ∈ ℚ⟮γ⟯ := by
  have hγ : γ ∈ ℚ⟮γ⟯ := mem_adjoin_simple_self ℚ γ
  have key : 2 * √6 = γ ^ 2 - 5:= two_sqrt_six_eq
  have key := congr($key/2)
  rw [show 2 * √6 / 2 = √6 by field_simp] at key
  rw [key]
  refine div_mem ?_ (by simp)
  refine sub_mem ?_ (by simp)
  · exact pow_mem hγ 2

noncomputable abbrev R : Subalgebra ℤ ℝ := Algebra.adjoin ℤ {γ}

theorem five_add_two_sqrt_six_mem : (5 : ℝ) + 2 * √6 ∈ R := by
  have hγ : γ ∈ R := Algebra.self_mem_adjoin_singleton ℤ γ
  have key : (5 : ℝ) + 2 * √6 = γ ^ 2 := by
    simp only [γ]
    sqrt_ring
  rw [key]
  exact pow_mem hγ 2
