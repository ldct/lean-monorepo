import Mathlib

set_option trace.debug true

def revRange : Nat → List Nat
  | 0     => []
  | n + 1 => n :: revRange n

#eval revRange 5 -- [4, 3, 2, 1, 0]

lemma revRange_zero : revRange 0 = [] := rfl
lemma revRange_succ (n : Nat) : revRange (n + 1) = n :: revRange n := rfl

dsimproc_decl revRangeCompute (revRange _) := fun e => do
  -- Extract the natural number from the expression
  let_expr revRange m ← e | return .continue
  -- Recover the natural number as a term of type `Nat`
  let some n := m.nat? | return .continue
  let l := revRange n
  -- Convert the list to an `Expr`
  let t1 := Lean.toExpr l
  trace[debug] t1
  return .done t1

example : revRange 5 = [4, 3, 2, 1, 0] := by
  show_term dsimp only [revRangeCompute]
