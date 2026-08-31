import IsoGraph

namespace IsoGraphPlayground.Subgraphs

@[inherit_doc] infix:50 " ↪ₛ " => CGraph.SubgraphOf
@[inherit_doc] infix:50 " ↪ᵢₛ " => CGraph.InducedSubgraphOf

def K9 : CGraph := CGraph.complete 9
def K5 : CGraph := K9.induce (fun v ↦ decide (v.1 % 2 = 0))
example : K5.V = {v : K9.V // decide (v.1 % 2 = 0)} := rfl
def K5_ind_K9 : K5 ↪ᵢₛ K9 := CGraph.InducedSubgraphOf.induce _ _
example : ⟦K5⟧ ≤ᵢₛ ⟦K9⟧ := ⟨ K5_ind_K9 ⟩

@[simp] lemma my_lemma (n : ℕ) (x y : (CGraph.complete n).V) :
    (CGraph.complete n).Adj x y = decide (x ≠ y) :=
  CGraph.complete_adj n x y

-- An induced subgraph of a complete graph is complete.
theorem CGraph.complete_of_inducedSubgraph
    {H : CGraph} {n : ℕ}
    (f : H ↪ᵢₛ (CGraph.complete n)) :
    (⟦H⟧ : IsoGraph) = IsoGraph.complete (FinEnum.card H.V) := by
  rw [IsoGraph.mk_eq_complete]
  intro x y hxy
  apply f.adj_map
  simp
  grind [f.injective]

theorem exists_cgraph_of_iso (H : IsoGraph) : ∃ H' : CGraph, ⟦H'⟧ = H := ⟨ H.toCGraph, IsoGraph.mk_toCGraph H ⟩

/-- An induced subgraph of a complete graph is complete. -/
theorem IsoGraph.complete_of_inducedSubgraph
    {H : IsoGraph} {n : ℕ}
    (f : H ≤ᵢₛ IsoGraph.complete n) :
    H = IsoGraph.complete H.V := by
  obtain ⟨ H, rfl ⟩ := exists_cgraph_of_iso H
  obtain ⟨f⟩ := f
  exact CGraph.complete_of_inducedSubgraph f

/- The type of bipartitions of a graph. -/
structure Bipartition (G : CGraph) where
  toFun : G.V → Bool
  valid : ∀ x y, G.Adj x y → toFun x ≠ toFun y

lemma Bipartition.nonempty_iff (G : CGraph) : Nonempty (Bipartition G) ↔ G.IsBipartite :=
  ⟨fun ⟨b⟩ ↦ ⟨b.toFun, b.valid⟩, fun ⟨c, hc⟩ ↦ ⟨⟨c, hc⟩⟩⟩

/-! The bipartition of a subgraph of bipartition -/
def bipartition_of_subgraph
  (H G : CGraph)
  (f : H ↪ₛ G)
  (g : Bipartition G)
  : Bipartition H where
  toFun v := g.toFun (f v)
  valid x y hxy := g.valid (f x) (f y) (f.map_adj hxy)

/- A subgraph of a bipartite graph is bipartite. -/
lemma CGraph.IsBipartite.of_subgraph
  {H G : CGraph}
  (f : H ↪ₛ G)
  (hG : G.IsBipartite)
  : H.IsBipartite := by
  obtain ⟨g⟩ := (Bipartition.nonempty_iff G).mpr hG
  exact (Bipartition.nonempty_iff H).mp ⟨bipartition_of_subgraph H G f g⟩

/- A subgraph of a bipartite graph is bipartite. -/
lemma IsoGraph.IsBipartite.of_subgraph
  (H G : IsoGraph)
  (f : H ≤ₛ G)
  (hG : G.IsBipartite)
  : H.IsBipartite := by
  obtain ⟨ H, rfl ⟩ := exists_cgraph_of_iso H
  obtain ⟨ G, rfl ⟩ := exists_cgraph_of_iso G
  obtain ⟨f⟩ := f
  rw [IsoGraph.isBipartite_mk] at *
  exact CGraph.IsBipartite.of_subgraph f hG


end IsoGraphPlayground.Subgraphs
