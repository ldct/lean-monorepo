/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Heap

/-! # Memory Safety Properties

Proofs that the heap model enforces basic memory safety invariants:
- `no_use_after_free`: a freed address cannot be looked up
- `no_double_free`: a freed address cannot be freed again
- `read_within_bounds`: in-bounds reads on a live allocation always succeed

These are properties of the `Heap` API, not of the full language -- they
show that the heap abstraction itself is sound. Full program-level memory
safety (e.g., "a well-typed program never performs use-after-free") would
require a linear type system or ownership tracking, which is future work.
-/

namespace Radix

/-- After freeing address `a`, looking it up returns `none`. -/
theorem Heap.no_use_after_free (h : Heap) (a : Addr) {h' : Heap}
    (hfree : h.free a = some h') : h'.lookup a = none := by
  unfold Heap.free at hfree
  split at hfree
  · simp at hfree
    unfold Heap.lookup
    rw [← hfree]
    simp
  · simp at hfree

/-- After freeing address `a`, freeing it again returns `none`. -/
theorem Heap.no_double_free (h : Heap) (a : Addr) {h' : Heap}
    (hfree : h.free a = some h') : h'.free a = none := by
  unfold Heap.free at hfree
  split at hfree
  · simp at hfree
    unfold Heap.free
    rw [← hfree]
    simp [Std.HashMap.contains_erase]
  · simp at hfree

/-- If `lookup` returns an array and `i` is within bounds, `read` succeeds. -/
theorem Heap.read_within_bounds (h : Heap) (a : Addr) (i : Nat) {arr : Array Value}
    (hlookup : h.lookup a = some arr) (hbounds : i < arr.size) :
    ∃ v, h.read a i = some v := by
  unfold Heap.read
  simp [hlookup, Array.getElem?_eq_getElem hbounds]

end Radix
