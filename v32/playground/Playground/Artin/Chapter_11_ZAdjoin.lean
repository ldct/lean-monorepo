import Playground.Artin.Chapter_11_1

-- Exercise 11.1.3
-- Headline result - (√2 : ℂ) ∉ ℤ[γ]

noncomputable abbrev γ : ℝ := √2 + √3

private noncomputable def coords (a b c d : ℤ) : ℂ :=
  (((a : ℝ) + b * √2 + c * √3 + d * √6 : ℝ) : ℂ)

private noncomputable def witness : Artin.CRing.Subring ℂ where
  carrier := {z | ∃ a b c d : ℤ, z = coords a b c d ∧ Even d ∧ Even (b - c)}
  one_mem' := by
    refine ⟨1, 0, 0, 0, ?_, by simp, by simp⟩
    simp [coords]
  neg_mem' := by
    rintro z ⟨a, b, c, d, rfl, hd, hbc⟩
    refine ⟨-a, -b, -c, -d, ?_, hd.neg, ?_⟩
    · simp only [coords]
      push_cast
      ring
    · rcases hbc with ⟨u, hu⟩
      refine ⟨-u, ?_⟩
      omega
  add_mem' := by
    rintro z z' ⟨a, b, c, d, rfl, hd, hbc⟩ ⟨a', b', c', d', rfl, hd', hbc'⟩
    refine ⟨a + a', b + b', c + c', d + d', ?_, hd.add hd', ?_⟩
    · simp only [coords]
      push_cast
      ring
    · rcases hbc with ⟨u, hu⟩
      rcases hbc' with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      omega
  mul_mem' := by
    rintro z z' ⟨a, b, c, d, rfl, hd, hbc⟩ ⟨a', b', c', d', rfl, hd', hbc'⟩
    let A := a*a' + 2*b*b' + 3*c*c' + 6*d*d'
    let B := a*b' + b*a' + 3*(c*d' + d*c')
    let C := a*c' + c*a' + 2*(b*d' + d*b')
    let D := a*d' + d*a' + b*c' + c*b'
    refine ⟨A, B, C, D, ?_, ?_, ?_⟩
    · change Complex.ofReal ((a : ℝ) + b * √2 + c * √3 + d * √6) *
          Complex.ofReal ((a' : ℝ) + b' * √2 + c' * √3 + d' * √6) =
          Complex.ofReal ((A : ℝ) + B * √2 + C * √3 + D * √6)
      rw [← Complex.ofReal_mul]
      apply congrArg Complex.ofReal
      dsimp [A, B, C, D]
      push_cast
      rw [show (√6 : ℝ) = √2 * √3 by sqrt_ring]
      have h2 : (√2 : ℝ) ^ 2 = 2 := by norm_num
      have h3 : (√3 : ℝ) ^ 2 = 3 := by norm_num
      ring_nf
      simp only [h2, h3]
      ring
    · rcases hd with ⟨x, hx⟩
      rcases hd' with ⟨y, hy⟩
      rcases hbc with ⟨u, hu⟩
      rcases hbc' with ⟨v, hv⟩
      have hb : b = c + (u + u) := by omega
      have hb' : b' = c' + (v + v) := by omega
      subst d
      subst d'
      subst b
      subst b'
      refine ⟨a*y + x*a' + c*c' + u*c' + c*v, ?_⟩
      dsimp [D]
      ring
    · rcases hd with ⟨x, hx⟩
      rcases hd' with ⟨y, hy⟩
      rcases hbc with ⟨u, hu⟩
      rcases hbc' with ⟨v, hv⟩
      have hb : b = c + (u + u) := by omega
      have hb' : b' = c' + (v + v) := by omega
      subst d
      subst d'
      subst b
      subst b'
      refine ⟨a*v + u*a' + c*y + x*c' - 4*u*y - 4*x*v, ?_⟩
      dsimp [B, C]
      ring

private lemma int_sqrt_two_independent (m n : ℤ)
    (h : (m : ℝ) + n * √2 = 0) : m = 0 ∧ n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · have hsqrt : Irrational (√2 : ℝ) := by norm_num
    have heq : (√2 : ℝ) = (-m : ℤ) / n := by
      push_cast
      field_simp
      linarith
    exact (hsqrt.ne_rational (-m) n heq).elim

example : ↑√2 ∉ ℤ[γ] := by
  intro h
  have hγ : (γ : ℂ) ∈ witness := by
    refine ⟨0, 1, 1, 0, ?_, by simp, by simp⟩
    simp only [coords, γ]
    push_cast
    ring
  have hs : (↑√2 : ℂ) ∈ witness := by
    exact (Artin.CRing.Subring.mem_IndexedIntersection.mp h) witness hγ
  rcases hs with ⟨a, b, c, d, heq, hd, hbc⟩
  have heqR : (√2 : ℝ) = (a : ℝ) + b * √2 + c * √3 + d * √6 := by
    simp only [coords] at heq
    exact_mod_cast heq
  have hsplit :
      (a : ℝ) + (b - 1) * √2 = -((c : ℝ) + d * √2) * √3 := by
    rw [show (√6 : ℝ) = √2 * √3 by sqrt_ring] at heqR
    nlinarith
  have hsquared := congrArg (fun x : ℝ => x ^ 2) hsplit
  have hsquared :
      ((a^2 + 2*(b-1)^2 - 3*c^2 - 6*d^2 : ℤ) : ℝ) +
        (2*a*(b-1) - 6*c*d : ℤ) * √2 = 0 := by
    have h2 : (√2 : ℝ) ^ 2 = 2 := by norm_num
    have h3 : (√3 : ℝ) ^ 2 = 3 := by norm_num
    ring_nf at hsquared
    rw [h2, h3] at hsquared
    push_cast
    ring_nf at hsquared ⊢
    nlinarith
  have hrat := (int_sqrt_two_independent _ _ hsquared).1
  rcases hd with ⟨x, hx⟩
  rcases hbc with ⟨u, hu⟩
  have hb : b = c + (u + u) := by omega
  subst d
  subst b
  rcases Int.even_or_odd' a with ⟨p, ha | ha⟩ <;>
    rcases Int.even_or_odd' c with ⟨q, hc | hc⟩ <;>
    subst a <;> subst c <;> ring_nf at hrat <;> omega
