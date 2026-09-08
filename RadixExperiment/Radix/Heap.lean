/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.AST
import Std.Data.HashMap

/-! # Radix Heap Model

A simple bump-allocator heap mapping addresses to `Array Value`. Each `alloc`
returns a fresh address (monotonically increasing `nextAddr`). The heap does
deallocate storage. `Radix.Proofs.MemorySafety` proves that execution preserves
existing allocation lengths, assuming the bump counter is initially fresh.

Heap reads and writes return `Option` to model failures
(invalid address, out-of-bounds index) explicitly.
-/

namespace Radix
open Std

/-- The heap: a map from addresses to arrays of values, plus a bump counter
for fresh address allocation. -/
structure Heap where
  store : HashMap Nat (Array Value) := {}
  nextAddr : Nat := 0
  deriving Inhabited

namespace Heap

def alloc (h : Heap) (vals : Array Value) : Addr × Heap :=
  let a := h.nextAddr
  (a, { store := h.store.insert a vals, nextAddr := a + 1 })

def lookup (h : Heap) (a : Addr) : Option (Array Value) :=
  h.store.get? a

def read (h : Heap) (a : Addr) (i : Nat) : Option Value := do
  let arr ← h.lookup a
  arr[i]?

def write (h : Heap) (a : Addr) (i : Nat) (v : Value) : Option Heap := do
  let arr ← h.lookup a
  if hi : i < arr.size then
    some { h with store := h.store.insert a (arr.set i v) }
  else
    none

def arraySize (h : Heap) (a : Addr) : Option Nat := do
  let arr ← h.lookup a
  return arr.size

end Heap
end Radix
