import Mathlib


namespace test

example (h : (1 : ZMod 4) = (2 : Fin (1 + 3)) ∨ 1 = (3 : Fin (2 + 2))) : False := by
  revert h
  decide

def one' : ZMod 4 := 1
def two' : ZMod 4 := 2
def three' : ZMod 4 := 3

example (h : one' = two' ∨ one' = three') : False := by
  simp_all [one', two', three']
  revert h
  decide

-- TODO: `one`, `two`, `three` were from LeanTeX or an old import; not available in v24
-- example (h : one = two ∨ one = three) : False := by
--   revert h
--   decide


end test