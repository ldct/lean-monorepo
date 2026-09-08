set_option autoImplicit false

/-- Elementary coverage of the corrected Theorem 9 five-interval split:
any naturals with `4*a*b < c` and `20*a*c < 3609*b^3` fall into one of the
five cases with the exact lower/upper boundaries (Case III uses the corrected
`c² ≤ 16*a^3*b^5` matching the detailed proof under label `thm:deg2`). -/
theorem pi_interval_coverage (a b c : Nat)
    (hlo : 4 * a * b < c) (hhi : a * c * 20 < 3609 * b ^ 3) :
    (4 * a * b < c ∧ c ^ 2 ≤ 16 * a * b ^ 3) ∨
    (16 * a * b ^ 3 < c ^ 2 ∧ c ≤ 4 * a * b ^ 2) ∨
    (4 * a * b ^ 2 < c ∧ c ^ 2 ≤ 16 * a ^ 3 * b ^ 5) ∨
    (16 * a ^ 3 * b ^ 5 < c ^ 2 ∧ c ≤ 4 * a ^ 2 * b ^ 3) ∨
    (4 * a ^ 2 * b ^ 3 < c ∧ a * c * 20 < 3609 * b ^ 3) := by
  rcases Decidable.em (c ^ 2 ≤ 16 * a * b ^ 3) with h1 | h1
  · exact Or.inl ⟨hlo, h1⟩
  · have g1 : 16 * a * b ^ 3 < c ^ 2 := Nat.lt_of_not_le h1
    rcases Decidable.em (c ≤ 4 * a * b ^ 2) with h2 | h2
    · exact Or.inr (Or.inl ⟨g1, h2⟩)
    · have g2 : 4 * a * b ^ 2 < c := Nat.lt_of_not_le h2
      rcases Decidable.em (c ^ 2 ≤ 16 * a ^ 3 * b ^ 5) with h3 | h3
      · exact Or.inr (Or.inr (Or.inl ⟨g2, h3⟩))
      · have g3 : 16 * a ^ 3 * b ^ 5 < c ^ 2 := Nat.lt_of_not_le h3
        rcases Decidable.em (c ≤ 4 * a ^ 2 * b ^ 3) with h4 | h4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g3, h4⟩)))
        · have g4 : 4 * a ^ 2 * b ^ 3 < c := Nat.lt_of_not_le h4
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨g4, hhi⟩)))

#print axioms pi_interval_coverage
