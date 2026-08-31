import IsoGraph

namespace IsoGraphPlayground

/-!
* `0`–`3`: outer top-left, top-right, bottom-right, bottom-left
* `4`–`7`: inner top-left, top-right, bottom-right, bottom-left
-/
def concreteCube : CGraph :=
  CGraph.ofEdges 8
    [ (0, 1), (1, 2), (2, 3), (3, 0) -- Outer square
    , (4, 5), (5, 6), (6, 7), (7, 4) -- Inner square
    , (0, 4), (1, 5), (2, 6), (3, 7) -- Corresponding corners
    ]

#check CGraph.isoSetoid

def cube : IsoGraph := ⟦concreteCube⟧

example : cube.V = 8 := by rfl
example : cube.E = 12 := by rfl

#decompose_graph cube


example : cube = IsoGraph.hypercube 3 := by native_decide

#check CGraph.E_complete

example (n : ℕ) : (IsoGraph.complete n).E = n.choose 2 := IsoGraph.E_complete n

#eval decide (IsoGraph.IsBipartite cube)

theorem cubeOfEdges_isBipartite : concreteCube.IsBipartite :=
  ⟨fun v ↦ (v.1 % 2 = v.1 / 4), by decide +revert⟩

example : cube.IsBipartite := by
  rw [cube, IsoGraph.isBipartite_mk]
  exact cubeOfEdges_isBipartite

end IsoGraphPlayground
