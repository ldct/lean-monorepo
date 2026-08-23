import Playground.Artin.SqrtRing

open IntermediateField Real

noncomputable abbrev γ : ℝ := √2 + √3

theorem five_add_sqrt_six_mem :  √6 ∈ ℚ⟮γ⟯ := by
  have hγ : γ ∈ ℚ⟮γ⟯ := mem_adjoin_simple_self ℚ γ
  rw [show √6 = (γ ^ 2 - 5) / 2 by sqrt_ring]
  aesop

theorem sqrt_six_mul_gamma_mem : √2 ∈ ℚ⟮γ⟯ := by
  have h1 :  √6 * (√2 + √3) ∈ ℚ⟮γ⟯ := by
    apply mul_mem
    · exact five_add_sqrt_six_mem
    exact mem_adjoin_simple_self ℚ γ
  rw [show √6 * (√2 + √3) = 2*√3 + 3*√2 by sqrt_ring] at h1
  have h2 : 2*(√2 + √3) ∈ ℚ⟮γ⟯ := by
    apply mul_mem
    · simp
    exact mem_adjoin_simple_self ℚ γ
  have h3 : 2 * √3 + 3 * √2 - (2 * (√2 + √3)) ∈ ℚ⟮γ⟯ := by
    grind [sub_mem]
  rw [show 2 * √3 + 3 * √2 - 2 * (√2 + √3) = √2 by linarith] at h3
  exact h3

noncomputable abbrev R : Subalgebra ℤ ℝ := Algebra.adjoin ℤ {γ}

theorem five_add_two_sqrt_six_mem : (5 : ℝ) + 2 * √6 ∈ R := by
  have hγ : γ ∈ R := Algebra.self_mem_adjoin_singleton ℤ γ
  have key : (5 : ℝ) + 2 * √6 = γ ^ 2 := by
    simp only [γ]
    sqrt_ring
  rw [key]
  exact pow_mem hγ 2
