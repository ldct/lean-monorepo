import Playground.RealIsometry

def IsCyclicOfOrder (n : ℕ) (G : Type*) [Group G] : Prop :=
  IsCyclic G ∧ Nat.card G = n

theorem RealIsometry.isCyclicOfOrder (n : ℕ) [NeZero n]
: ∃ f : Subgroup RealIsometry, IsCyclicOfOrder n f := by
  sorry
