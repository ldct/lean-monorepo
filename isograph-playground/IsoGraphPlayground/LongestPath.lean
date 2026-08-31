import IsoGraph
import IsoGraph.Containment.Algorithms.Cached

namespace IsoGraph

/-! # Longest induced paths and circumference -/

/-- `n` is the order of an induced path in `G`. -/
def IsPathOrder (G : IsoGraph) (n : ℕ) : Prop :=
  path n ≤ᵢₛ G

/-- Induced path containment is decidable by IsoGraph's cached containment
algorithm. -/
instance (G : IsoGraph) : DecidablePred G.IsPathOrder :=
  fun n ↦ instDecidableIsInducedSubgraphOf (path n) G

/-- The possible orders (numbers of vertices) of induced path subgraphs of `G`.
Restricting to `G.V + 1` makes the set manifestly finite. -/
def pathOrders (G : IsoGraph) : Finset ℕ :=
  (Finset.range (G.V + 1)).filter G.IsPathOrder

/-- The order of a longest induced path subgraph of `G`. -/
def longestPathOrder (G : IsoGraph) : ℕ :=
  G.pathOrders.sup id

/-- A canonical representative of a longest induced path subgraph of `G`.
For the empty graph this is `path 0`. -/
def longestPath (G : IsoGraph) : IsoGraph :=
  path G.longestPathOrder

/-- The length (number of edges) of a longest path in `G`. -/
def longestPathLength (G : IsoGraph) : ℕ :=
  G.longestPathOrder - 1

/-- The selected longest path is an induced subgraph of `G`. -/
theorem longestPath_isInducedSubgraphOf (G : IsoGraph) : G.longestPath ≤ᵢₛ G := by
  have hne : G.pathOrders.Nonempty := by
    refine ⟨0, ?_⟩
    rw [pathOrders, Finset.mem_filter]
    exact ⟨by simp, by simpa [IsPathOrder] using empty_zero_isInducedSubgraphOf G⟩
  have hmem : G.longestPathOrder ∈ G.pathOrders := by
    rcases Finset.sup_mem_of_nonempty (f := id) hne with ⟨n, hn, h⟩
    simpa [longestPathOrder] using h ▸ hn
  exact (Finset.mem_filter.mp hmem).2

/-- No induced path subgraph of `G` has more vertices than `G.longestPath`. -/
theorem pathOrder_le_longestPathOrder {G : IsoGraph} {n : ℕ} (h : path n ≤ᵢₛ G) :
    n ≤ G.longestPathOrder := by
  have hnV : n ≤ G.V := by simpa using h.V_le
  apply Finset.le_sup (f := id)
  rw [pathOrders, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by omega), h⟩

/-- The possible lengths of cycle subgraphs of `G`.

A cycle has equally many vertices and edges.  We require length at least three,
as usual for cycles in a simple graph. -/
def cycleLengths (G : IsoGraph) : Finset ℕ :=
  (Finset.range (G.V + 1)).filter fun n ↦ 3 ≤ n ∧ cycle n ≤ₛ G

/-- The circumference of `G`: the greatest length of a cycle subgraph, or zero
when `G` is acyclic. -/
def circumference (G : IsoGraph) : ℕ :=
  G.cycleLengths.sup id

/-- Every cycle subgraph has length at most the circumference. -/
theorem cycleLength_le_circumference {G : IsoGraph} {n : ℕ} (hn : 3 ≤ n)
    (h : cycle n ≤ₛ G) : n ≤ G.circumference := by
  have hnV : n ≤ G.V := by simpa using h.V_le
  apply Finset.le_sup (f := id)
  rw [cycleLengths, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (by omega), hn, h⟩

/-! ## Snake-in-the-box values -/

/-- The zero-dimensional cube has only one vertex. -/
theorem longestPathLength_hypercube_zero : (hypercube 0).longestPathLength = 0 := by
  native_decide

/-- The first nontrivial snake-in-the-box value. -/
theorem longestPathLength_hypercube_one : (hypercube 1).longestPathLength = 1 := by
  native_decide

theorem longestPathLength_hypercube_two : (hypercube 2).longestPathLength = 2 := by
  native_decide

theorem longestPathLength_hypercube_three : (hypercube 3).longestPathLength = 4 := by
  native_decide

theorem longestPathLength_hypercube_four : (hypercube 4).longestPathLength = 7 := by
  native_decide

theorem longestPathLength_hypercube_five : (hypercube 5).longestPathLength = 13 := by
  native_decide

end IsoGraph
