import IsoGraph
import IsoGraphPlayground.Subgraphs

example : IsoGraph.lineGraph (IsoGraph.bipartite 3 3) = IsoGraph.rook 3 3 := by
  simp

#check CGraph.disjUnion

example : IsoGraph.lineGraph (IsoGraph.bipartite 3 3) = IsoGraph.rook 3 3 := by simp
example : IsoGraph.petersen = IsoGraph.kneser 5 2 := rfl


#check CGraph

#check CGraph.ofEdges
