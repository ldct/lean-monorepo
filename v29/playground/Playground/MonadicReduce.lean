set_option maxRecDepth 3000000
set_option maxHeartbeats 2000000

/-!
# Imperative `#reduce` via Id monad

`do` notation with `let mut` and `for` loops desugars to `forIn` calls
that thread state through closures. This creates the same unevaluated
`Nat.add` chain as a plain fold.

Forcing the accumulator via `match` inside the loop fixes the Nat chain,
raising the limit from ~7500 to ~20000. But the `forIn` closure nesting
itself still causes O(n) depth in expression equality checking, so it
can't match plain recursion with pattern matching (~1M).
-/

/-! ### Plain Id + for: same ~7500 Nat.add chain limit -/

def imperativeSum (n : Nat) : Id Nat := do
  let mut acc := 0
  for i in List.range n do
    acc := acc + i
  return acc

#reduce imperativeSum 3000          -- ✓
-- #reduce imperativeSum 7000       -- ✗ Stack overflow

/-! ### Forced accumulator inside loop: ~20000 limit -/

def imperativeSumForce (n : Nat) : Id Nat := do
  let mut acc := 0
  for i in List.range n do
    acc := acc + i
    match acc with
    | 0 => acc := 0
    | k + 1 => acc := k + 1
  return acc

#reduce imperativeSumForce 10000    -- ✓ 49995000
-- #reduce imperativeSumForce 30000 -- ✗ deep recursion at 'expression equality test'
