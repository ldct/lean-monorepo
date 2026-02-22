import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Log
import Mathlib.Order.WithBot
import Plausible

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

-- minimum of xs[l..r] inclusive
def rmqNaive (xs : Array ℕ) (l r : ℕ) : WithTop ℕ :=
  (xs.drop l |>.take (r - l + 1)).toList.minimum

/-
# Sparse Table

Define a structure SparseTable which preprocesses an array of integers for fast RMQ queries.
- make : Array ℕ → SparseTable
- query : SparseTable → ℕ → ℕ → ℕ
-/

structure SparseTable where
  table : Array (Array ℕ)

def SparseTable.make (a : Array ℕ) : SparseTable := {
  table :=
    if a.size == 0 then #[]
    else Id.run do
      let n := a.size
      let k := Nat.log 2 n + 1
      let mut st : Array (Array ℕ) := #[a]
      for i in [1:k] do
        let half := 2 ^ (i - 1)
        let rowLen := n - 2 ^ i + 1
        let prev := st[i - 1]!
        let mut row : Array ℕ := Array.mkEmpty rowLen
        for j in [:rowLen] do
          row := row.push (min prev[j]! prev[j + half]!)
        st := st.push row
      return st
}

def SparseTable.query (st : SparseTable) (l r : ℕ) : ℕ :=
  let len := r - l + 1
  let k := Nat.log 2 len
  min st.table[k]![l]! st.table[k]![r + 1 - 2 ^ k]!

/-
# Internal verification

Verify that SparseTable generates the correct table as the python code (verification by eval'ing examples).
Expected values obtained via: echo "3 1 4 1 5 9 2 6" | python3 sparsetable.py
-/

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[3, 1, 4, 1, 5, 9, 2, 6]).table == #[#[3, 1, 4, 1, 5, 9, 2, 6], #[1, 1, 1, 1, 5, 2, 2], #[1, 1, 1, 1, 2], #[1]]

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[5]).table == #[#[5]]

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[10, 20]).table == #[#[10, 20], #[10]]

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[7, 2, 9, 4, 3, 1, 8]).table == #[#[7, 2, 9, 4, 3, 1, 8], #[2, 2, 4, 3, 1, 1], #[2, 2, 1, 1]]

/-
# Verification
-/
theorem correct (vals : Array ℕ) (l r : ℕ) (h : l ≤ r) (hr : r < vals.size)
: (SparseTable.make vals).query l r = rmqNaive vals l r := by plausible

def randArray (size : ℕ) : IO (Array ℕ) := do
  let mut arr : Array ℕ := #[]
  for _ in [:size] do
    let v ← IO.rand 0 200
    arr := arr.push v
  return arr

def SparseTable.verifyOne (vals : Array ℕ) : Bool :=
  let st := SparseTable.make vals
  Id.run do
    let mut ok := true
    for l in [:vals.size] do
      for r in [l:vals.size] do
        if rmqNaive vals l r != ↑(st.query l r) then
          ok := false
    return ok

def SparseTable.verify : IO Bool := do
  IO.setRandSeed 42
  let mut ok := true
  for sz in [1:51] do
    let arr ← randArray sz
    if !SparseTable.verifyOne arr then
      ok := false
  return ok

#eval SparseTable.verify



end Cslib.Algorithms.Lean.TimeM
