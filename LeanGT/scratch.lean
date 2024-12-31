import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import LeanGT.ZMul

-- pg 52, q2
example [Group G] : Subgroup.centralizer (Subgroup.center G).carrier = ⊤ := by
  exact Subgroup.centralizer_eq_top_iff_subset.mpr fun ⦃a⦄ a ↦ a

-- reprove the above theorem
-- D&F pg 52, q2. Note that `exact?` also solves this.
example [Group G] : Subgroup.centralizer (Subgroup.center G).carrier = ⊤ := by
  rw [eq_top_iff] -- use some lattice theory to rewrite as ⊤ ≤ ...
  intro g _ h h_in_center
  exact h_in_center.comm g

example [Lattice L] [OrderTop L] (a b c : L) : a ≤ b → b ≤ c → a ≤ c := by
  exact fun a_1 a_2 ↦ Preorder.le_trans a b c a_1 a_2

example [Lattice L] [OrderTop L] (a: L) : ⊤ ≤ a → a = ⊤ := by
  rw [eq_top_iff]
  exact fun a ↦ a

theorem C_Z_ge_top [Group G] : Subgroup.centralizer (Subgroup.center G).carrier ≥ ⊤ := by
  intro g _ h h_in_center
  exact h_in_center.comm g

example [Group G] : Subgroup.centralizer (Subgroup.center G).carrier = ⊤ := by
  have : Subgroup.centralizer (Subgroup.center G).carrier ≤ ⊤ := by exact fun ⦃x⦄ a ↦ trivial
  sorry

example [Lattice L] [OrderTop L] (a b c : L) : a ≤ b → b ≤ c → a ≤ c := by
  exact fun a_1 a_2 ↦ Preorder.le_trans a b c a_1 a_2

example [Lattice L] [OrderTop L] (a: L) : a ≥ ⊤ → a = ⊤ := by
  exact?



example [Group G] (A B : Set G) (A_le_B : A ≤ B) : Subgroup.centralizer (B) ≤ Subgroup.centralizer A := by
  exact Subgroup.centralizer_le A_le_B
