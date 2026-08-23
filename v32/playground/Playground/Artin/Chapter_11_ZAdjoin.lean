import Playground.Artin.Chapter_11_1


lemma sqrt_three_ne_quad (x y : ℚ) : (√3 : ℝ) ≠ x + y * √2 := by
  intro h
  have hsq := congrArg (fun z : ℝ => z ^ 2) h
  have hsq' : (3 : ℝ) = (x : ℝ) ^ 2 + 2 * (y : ℝ) ^ 2 + (2 * (x : ℝ) * y) * √2 := by
    rw [show (3 : ℝ) = (√3 : ℝ) ^ 2 by norm_num]
    rw [h]
    sqrt_ring
  by_cases hxy : x * y = 0
  · rcases mul_eq_zero.mp hxy with hx | hy
    · have h' : (√3 : ℝ) = 0 + y * √2 := by simpa [hx] using h
      have h6 : (√6 : ℝ) = (2 * y : ℚ) := by
        calc
          (√6 : ℝ) = √3 * √2 := by sqrt_ring
          _ = (0 + y * √2) * √2 := by rw [h']
          _ = (2 * y : ℚ) := by
            push_cast
            sqrt_ring
      exact (show Irrational (√(6 : ℝ)) by norm_num).ne_rat (2*y) h6
    · have h' : (√3 : ℝ) = x + 0 * √2 := by simpa [hy] using h
      exact (show Irrational (√(3 : ℝ)) by norm_num).ne_rat x (by simpa using h')
  · have hr : (√2 : ℝ) = ((3 : ℚ) - x^2 - 2*y^2) / (2*x*y) := by
      apply (eq_div_iff (by
        norm_cast
        exact mul_ne_zero (mul_ne_zero (by norm_num) (by
          intro hx
          apply hxy
          simp [hx])) (by
          intro hy
          apply hxy
          simp [hy]))).2
      push_cast
      nlinarith [hsq']
    exact irrational_sqrt_two.ne_rat ((3 - x^2 - 2*y^2) / (2*x*y)) (by
      convert hr using 1 <;> push_cast <;> ring)

lemma rat_sqrt_two_eq_zero (x y : ℚ) (h : (x : ℝ) + y * √2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · refine ⟨?_, hy⟩
    simpa [hy] using h
  · exfalso
    apply irrational_sqrt_two.ne_rat (-x / y)
    have hr : (√2 : ℝ) = (-(x : ℝ)) / y := by
      apply (eq_div_iff (by exact_mod_cast hy)).2
      push_cast
      linarith
    convert hr using 1 <;> push_cast <;> ring

lemma radical_linear_independent (a b c d : ℚ)
    (h : (a : ℝ) + b * √2 + c * √3 + d * √6 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hmul : ((c : ℝ) + d * √2) * √3 = -((a : ℝ) + b * √2) := by
    rw [show (√6 : ℝ) = √2 * √3 by sqrt_ring] at h
    linear_combination h
  by_cases hq : (c : ℝ) + d * √2 = 0
  · obtain ⟨hc, hd⟩ := rat_sqrt_two_eq_zero c d hq
    subst c
    subst d
    have hab : (a : ℝ) + b * √2 = 0 := by simpa using h
    obtain ⟨ha, hb⟩ := rat_sqrt_two_eq_zero a b hab
    simp [ha, hb]
  · have hq' : (c : ℝ) - d * √2 ≠ 0 := by
      intro hq'
      have hzero : (c : ℝ) + (-d) * √2 = 0 := by
        push_cast
        linarith [hq']
      obtain ⟨hc, hd⟩ := rat_sqrt_two_eq_zero c (-d) (by simpa using hzero)
      have hd' : d = 0 := neg_eq_zero.mp hd
      apply hq
      simp [hc, hd']
    have hden : (c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2 ≠ 0 := by
      rw [show (c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2 =
        ((c : ℝ) + d * √2) * ((c : ℝ) - d * √2) by sqrt_ring]
      exact mul_ne_zero hq hq'
    have hs3 : (√3 : ℝ) =
        ((-a*c + 2*b*d : ℚ) / (c^2 - 2*d^2)) +
          ((a*d - b*c : ℚ) / (c^2 - 2*d^2)) * √2 := by
      calc
        (√3 : ℝ) =
            ((-(a : ℝ) * c + 2 * b * d) + ((a : ℝ) * d - b * c) * √2) /
              ((c : ℝ)^2 - 2 * (d : ℝ)^2) := by
          apply (eq_div_iff hden).2
          rw [show (c : ℝ)^2 - 2 * (d : ℝ)^2 =
            ((c : ℝ) + d * √2) * ((c : ℝ) - d * √2) by sqrt_ring]
          calc
            √3 * (((c : ℝ) + d * √2) * ((c : ℝ) - d * √2)) =
                (((c : ℝ) + d * √2) * √3) * ((c : ℝ) - d * √2) := by ring
            _ = (-((a : ℝ) + b * √2)) * ((c : ℝ) - d * √2) := by rw [hmul]
            _ = (-(a : ℝ) * c + 2 * b * d) + ((a : ℝ) * d - b * c) * √2 := by
              sqrt_ring
        _ = ((-a*c + 2*b*d : ℚ) / (c^2 - 2*d^2)) +
          ((a*d - b*c : ℚ) / (c^2 - 2*d^2)) * √2 := by
            field_simp
            push_cast
            ring
    have hs3' : (√3 : ℝ) =
        (((-a*c + 2*b*d : ℚ) / (c^2 - 2*d^2) : ℚ) : ℝ) +
          (((a*d - b*c : ℚ) / (c^2 - 2*d^2) : ℚ) : ℝ) * √2 := by
      convert hs3 using 1 <;> push_cast <;> ring
    exact (sqrt_three_ne_quad _ _ hs3').elim


lemma radical_mul (a b c d e f g h : ℝ) :
  (a+b*√2+c*√3+d*√6)*(e+f*√2+g*√3+h*√6) =
    (a*e+2*b*f+3*c*g+6*d*h) +
    (a*f+b*e+3*c*h+3*d*g)*√2 +
    (a*g+c*e+2*b*h+2*d*f)*√3 +
    (a*h+d*e+b*g+c*f)*√6 := by
  calc
    _ = a*e + a*f*√2 + a*g*√3 + a*h*√6 + b*e*√2 + b*f*(√2*√2) +
        b*g*(√2*√3) + b*h*(√2*√6) + c*e*√3 + c*f*(√3*√2) +
        c*g*(√3*√3) + c*h*(√3*√6) + d*e*√6 + d*f*(√6*√2) +
        d*g*(√6*√3) + d*h*(√6*√6) := by ring
    _ = _ := by
      rw [show (√2 : ℝ) * √2 = 2 by norm_num,
        show (√3 : ℝ) * √3 = 3 by norm_num,
        show (√6 : ℝ) * √6 = 6 by norm_num,
        show (√2 : ℝ) * √3 = √6 by sqrt_ring,
        show (√2 : ℝ) * √6 = 2 * √3 by sqrt_ring,
        show (√3 : ℝ) * √6 = 3 * √2 by sqrt_ring,
        show (√3 : ℝ) * √2 = √6 by sqrt_ring,
        show (√6 : ℝ) * √2 = 2 * √3 by sqrt_ring,
        show (√6 : ℝ) * √3 = 3 * √2 by sqrt_ring]
      ring


noncomputable abbrev γ : ℝ := √2 + √3



example : (√2 : ℂ) ∉ ℤ[γ] := by
  let S : Artin.CRing.Subring ℂ :=
    { carrier := {z | ∃ a b c d : ℤ,
        z = ↑((a : ℝ) + b * (√2 + √3) + c * (2 * √2) + d * (2 * √6)) }
      one_mem' := by
        refine ⟨1, 0, 0, 0, ?_⟩
        norm_num
      neg_mem' := by
        rintro z ⟨a, b, c, d, hz⟩
        refine ⟨-a, -b, -c, -d, ?_⟩
        rw [hz]
        push_cast
        ring
      add_mem' := by
        rintro z w ⟨a, b, c, d, hz⟩ ⟨e, f, g, h, hw⟩
        refine ⟨a + e, b + f, c + g, d + h, ?_⟩
        rw [hz, hw]
        push_cast
        ring
      mul_mem' := by
        rintro z w ⟨a, b, c, d, hz⟩ ⟨e, f, g, h, hw⟩
        refine ⟨a*e + 5*b*f + 4*b*g + 8*c*g + 4*c*f + 24*d*h,
          a*f + b*e + 4*b*h + 8*c*h + 4*d*f + 8*d*g,
          a*g + c*e + b*h - 4*c*h + d*f - 4*d*g,
          a*h + d*e + b*f + b*g + c*f, ?_⟩
        rw [hz, hw]
        have hreal :
            ((a : ℝ) + b * (√2 + √3) + c * (2 * √2) + d * (2 * √6)) *
              ((e : ℝ) + f * (√2 + √3) + g * (2 * √2) + h * (2 * √6)) =
            ((a*e + 5*b*f + 4*b*g + 8*c*g + 4*c*f + 24*d*h : ℤ) : ℝ) +
              ((a*f + b*e + 4*b*h + 8*c*h + 4*d*f + 8*d*g : ℤ) : ℝ) * (√2 + √3) +
              ((a*g + c*e + b*h - 4*c*h + d*f - 4*d*g : ℤ) : ℝ) * (2 * √2) +
              ((a*h + d*e + b*f + b*g + c*f : ℤ) : ℝ) * (2 * √6) := by
          calc
            _ = ((a : ℝ) + (b + 2*c) * √2 + b * √3 + (2*d) * √6) *
                ((e : ℝ) + (f + 2*g) * √2 + f * √3 + (2*h) * √6) := by ring
            _ = _ := by
              rw [radical_mul]
              push_cast
              ring
        exact_mod_cast hreal }
  intro h
  have hS : (↑√2 : ℂ) ∈ S :=
    Artin.CRing.Subring.mem_IndexedIntersection.mp h S (by
      change (↑γ : ℂ) ∈ S
      refine ⟨0, 1, 0, 0, ?_⟩
      norm_num [γ])
  rcases hS with ⟨a, b, c, d, hS⟩
  have hS' : (√2 : ℝ) =
      (a : ℝ) + b * (√2 + √3) + c * (2 * √2) + d * (2 * √6) := by
    exact_mod_cast hS
  have hlin : ((a : ℚ) : ℝ) + ((b + 2*c - 1 : ℤ) : ℚ) * √2 +
      ((b : ℚ) : ℝ) * √3 + ((2*d : ℤ) : ℚ) * √6 = 0 := by
    push_cast
    linarith [hS']
  obtain ⟨ha, hb, hc, hd⟩ := radical_linear_independent
    (a : ℚ) ((b + 2*c - 1 : ℤ) : ℚ) (b : ℚ) ((2*d : ℤ) : ℚ) hlin
  norm_cast at hb hc
  omega

namespace Artin
end Artin
