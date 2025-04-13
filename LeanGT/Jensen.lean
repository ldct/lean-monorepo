import Mathlib

-- Jensen's inequality for 2 points
theorem two_point_jensen
(a b : ℝ)
(D : Set ℝ)
(ha : a ∈ D)
(hb : b ∈ D)
(f : ℝ → ℝ)
(f_convex : ConvexOn ℝ D f)
: f (1 / 2 * a + 1 / 2 * b) ≤ 1 / 2 * f a + 1 / 2 * f b
:= by
  have hc : ConvexOn ℝ D f := by
    exact f_convex

  let w : Fin 2 → ℝ := fun _ => (1:ℝ)/2

  let p : Fin 2 → ℝ := fun i =>
      match i with
      | 0 => a
      | 1 => b

  let s : Finset (Fin 2) := Finset.univ

  have hw : ∀ i ∈ s, 0 ≤ w i := by
      intro i hi
      fin_cases i <;> positivity

  have hw' : ∑ i ∈ s, w i = 1 := by
      rw [Fin.sum_univ_two]
      unfold w
      norm_num

  have hmem : ∀ i ∈ s, p i ∈ D := by
      intro i hi
      fin_cases i
      simp
      rw [show p 0 = a by rfl]
      exact ha
      rw [show p 1 = b by rfl]
      exact hb

  have jensens := f_convex.map_sum_le hw hw' hmem

  unfold s at jensens
  simp at jensens

  unfold w at jensens

  rw [show p 0 = a by rfl, show p 1 = b by rfl] at jensens

  exact jensens
