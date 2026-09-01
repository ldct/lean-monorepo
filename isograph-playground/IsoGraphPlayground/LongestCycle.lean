import IsoGraph
import IsoGraph.Containment.Algorithms.Cached

namespace IsoGraph

/-! # Longest cycles and circumference -/

/-- The possible lengths of cycle subgraphs of `G`.

A cycle has equally many vertices and edges. We require length at least three,
as usual for cycles in a simple graph. -/
def cycleLengths (G : IsoGraph) : Finset ℕ :=
  (Finset.range (G.V + 1)).filter fun n ↦ 3 ≤ n ∧ cycle n ≤ₛ G

/-- The circumference of `G`: the greatest length of a cycle subgraph, or zero
when `G` is acyclic. -/
def circumference (G : IsoGraph) : ℕ :=
  G.cycleLengths.sup id

#check (IsoGraph.path 3).girth

example : (IsoGraph.path 3).girth = 0 := by
  simp

example : (IsoGraph.path 3).circumference = 0 := by
  native_decide

/-- Every cycle subgraph has length at most the circumference. -/
theorem cycleLength_le_circumference {G : IsoGraph} {n : ℕ} (hn : 3 ≤ n)
    (h : cycle n ≤ₛ G) : n ≤ G.circumference := by
  have hnV : n ≤ G.V := by simpa using h.V_le
  apply Finset.le_sup (f := id)
  rw [cycleLengths, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by omega), hn, h⟩

end IsoGraph
