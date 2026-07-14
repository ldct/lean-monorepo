import Playground.Analysis.TendsTo

-- def Monotone: we use the Mathlib defn

namespace MonotoneConvergence

def BoundedAbove (a : ℕ → ℝ) : Prop := ∃ B, ∀ n, a n ≤ B

-- Monotone Convergence Theorem: an increasing bounded sequence converges
theorem MCT_formula
  {a : ℕ → ℝ}
  (a_inc : Monotone a)
  (a_bdd : BoundedAbove a)
: TendsTo a (sSup { a n | n : ℕ}) := by
  let as := { a n | n : ℕ}
  let s := sSup as
  obtain ⟨B, a_bdd⟩ := a_bdd
  have as_Bdd : BddAbove as := by
    use B
    unfold upperBounds
    rintro e ⟨ n, hn ⟩
    exact le_of_eq_of_le (Eq.symm hn) (a_bdd n)
  have as_Nonempty : as.Nonempty := by use (a 0), 0
  have s_IsLUB : IsLUB as s := by
    exact Real.isLUB_sSup as_Nonempty as_Bdd
  intro ε hε
  have s_is_ub : s ∈ upperBounds as := by
    exact Set.mem_of_mem_inter_left s_IsLUB
  have : (s - ε) ∉ upperBounds as := by
    rw [IsLUB, IsLeast] at s_IsLUB
    have t := s_IsLUB.right
    unfold lowerBounds at t
    simp only [Set.mem_setOf_eq] at t
    by_contra l_ε_ub
    specialize t l_ε_ub
    linarith
  unfold upperBounds at this
  simp only [Set.mem_setOf_eq, not_forall, not_le] at this
  obtain ⟨aN, haN⟩ := this
  obtain ⟨aN_in_s, haN⟩ := haN
  obtain ⟨N, hN⟩ := aN_in_s
  rw [← hN] at haN
  use N
  intro n hn
  have : a N ≤ a n := a_inc hn
  rw [show sSup {x | ∃ n, a n = x} = s by exact rfl]
  rw [abs_lt]
  constructor
  · linarith
  · have : (a n) ∈ as := by use n
    have : a n ≤ s := by exact s_is_ub this
    linarith

theorem MCT
  {a : ℕ → ℝ}
  (a_inc : Monotone a)
  (a_bdd : BoundedAbove a)
: Converges a := by
  use (sSup { a n | n : ℕ})
  exact MCT_formula a_inc a_bdd


end MonotoneConvergence
