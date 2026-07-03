import Mathlib


namespace Jensen

/-- Jensen's inequality for 2 points
For a function f : ℝ → ℝ that is convex on a set D,
f (1/2 * a + 1/2 * b) ≤ 1/2 * f a + 1/2 * f b
where a, b ∈ D
-/
theorem two_point_jensen
(a b : ℝ)
(D : Set ℝ)
(ha : a ∈ D)
(hb : b ∈ D)
(f : ℝ → ℝ)
(f_convex : ConvexOn ℝ D f)
: f (1 / 2 * a + 1 / 2 * b) ≤ 1 / 2 * f a + 1 / 2 * f b
:= by
  let w (_ : Fin 2) := (1 : ℝ) / 2
  let p := ![a, b]
  let s : Finset (Fin 2) := .univ
  have hw : ∀ i ∈ s, 0 ≤ w i := by
    intro i hi
    grind
  have hw' : ∑ i ∈ s, w i = 1 := by grind [Fin.sum_univ_two]
  have hmem : ∀ i ∈ s, p i ∈ D := by
    intro i hi
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [show p 0 = a by rfl]
      exact ha
    · dsimp
      rw [show p 1 = b by rfl]
      exact hb
  have jensens := f_convex.map_sum_le hw hw' hmem
  unfold s at jensens
  simp only [smul_eq_mul, Fin.sum_univ_two, Fin.isValue] at jensens
  unfold w at jensens
  rw [show p 0 = a by rfl, show p 1 = b by rfl] at jensens
  exact jensens

theorem tpu
(a b : ℝ)
(f : ℝ → ℝ)
(f_convex : ConvexOn ℝ ⊤ f)
: f (1 / 2 * a + 1 / 2 * b) ≤ 1 / 2 * f a + 1 / 2 * f b
:= by
  let w (_ : Fin 2) : ℝ := (1:ℝ)/2
  let p (i : Fin 2) : ℝ :=
    match i with
    | 0 => a
    | 1 => b
  have hw' : ∑ i ∈ .univ, w i = 1 := by grind [Fin.sum_univ_two]
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin 2)), p i ∈ (.univ : Set ℝ) := by grind
  have jensens := f_convex.map_sum_le (by grind) hw' hmem
  simp only [smul_eq_mul, Fin.sum_univ_two, Fin.isValue] at jensens
  unfold w at jensens
  rw [show p 0 = a by rfl, show p 1 = b by rfl] at jensens
  exact jensens


end Jensen
