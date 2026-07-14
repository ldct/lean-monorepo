/-!
# Kernel TCO Investigation

The kernel's `whnf` handles recursive function unfolding iteratively via a
while-loop, so function calls themselves don't grow the C++ stack.

The bottleneck is **reducing nested `Nat.add` chains**. `reduce_nat` handles
`Nat.add a b` by calling `whnf(a)` and `whnf(b)`. If an argument is itself
a `Nat.add`, this recurses. A chain of N nested additions requires O(N) stack.

Tail recursion doesn't help: the kernel does NOT eagerly reduce the accumulator.
`natSumTR n (acc + n + 1)` passes `acc + n + 1` unevaluated. After n steps the
accumulator is `((((0 + n) + (n-1)) + ...) + 1)` — a chain requiring O(n) stack.

The fix: pattern-match the accumulator to force the kernel to reduce it to a
literal at each step. This is analogous to strict foldl in Haskell.
-/

set_option maxRecDepth 3000000
set_option maxHeartbeats 2000000

/-! ### Non-tail-recursive sum: O(n) stack -/

def natSum : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + natSum n

-- Produces right-nested chain: n + ((n-1) + ... + (1 + 0))
-- Each Nat.add needs whnf of its right arg → O(n) recursive whnf calls
#reduce natSum 3000       -- ✓
-- #reduce natSum 8000    -- ✗ Stack overflow

/-! ### Tail-recursive sum: still O(n) stack -/

def natSumTR : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => natSumTR n (acc + n + 1)

-- Accumulator is never pattern-matched, so it builds up unevaluated:
-- ((((0 + n + 1) + (n-1) + 1) + ...) + 1 + 1)
-- Two additions per step → chain of ~2n → crashes at ~n=5000
#reduce natSumTR 2000 0   -- ✓
-- #reduce natSumTR 5100 0 -- ✗ Stack overflow

/-! ### Forced-accumulator sum: O(1) stack -/

-- By matching on acc, we force the kernel to reduce it to a Nat literal
-- (0 or Nat.succ n) BEFORE recursing. Since both operands of each Nat.add
-- are then literals, the built-in reduce_nat handles each step in O(1) stack.
def sumForce : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, 0 => sumForce xs x
  | x :: xs, (n + 1) => sumForce xs (n + 1 + x)

#reduce sumForce (List.range 10000) 0      -- ✓ 49995000
#reduce sumForce (List.range 100000) 0     -- ✓ 4999950000
-- #reduce sumForce (List.range 1000000) 0    -- ✓ 499999500000
