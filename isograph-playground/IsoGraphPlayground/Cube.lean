import IsoGraph

namespace IsoGraphPlayground

inductive CubeVertex
  | outer (i : Fin 4)
  | inner (i : Fin 4)
  deriving DecidableEq, Repr

open CubeVertex

instance : FinEnum CubeVertex :=
  FinEnum.ofList
    [ outer 0, outer 1, outer 2, outer 3
    , inner 0, inner 1, inner 2, inner 3
    ] (by
      intro v
      cases v
      simp
      grind
      simp
      grind)

def cubeAdj : CubeVertex → CubeVertex → Bool
  | outer 0, outer 1
  | outer 1, outer 0
  | outer 1, outer 2
  | outer 2, outer 1
  | outer 2, outer 3
  | outer 3, outer 2
  | outer 3, outer 0
  | outer 0, outer 3
  | .inner 0, .inner 1
  | .inner 1, .inner 0
  | .inner 1, .inner 2
  | .inner 2, .inner 1
  | .inner 2, .inner 3
  | .inner 3, .inner 2
  | .inner 3, .inner 0
  | .inner 0, .inner 3 => true
  | .outer x, .inner y => (x == y)
  | .inner x, .outer y => (x == y)
  | _, _ => false

def concreteCube : CGraph where
  V := CubeVertex
  Adj := cubeAdj
  symm u v := by decide +revert
  loopless v := by decide +revert

def cube : IsoGraph := ⟦concreteCube⟧

example : cube = .hypercube 3 := by
  native_decide -- decompose_graph to print the answer

end IsoGraphPlayground
