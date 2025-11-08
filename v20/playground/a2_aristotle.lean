/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Your Lean code is run in a custom environment, which uses these headers:

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

The following was proved by Aristotle:

- example : (fun x ↦ x + 1) '' { 1, 2, 3} = { 2, 3, 4}
-/

import Mathlib


#eval List.map (fun x ↦ x + 1) [1, 2, 3]

example : List.map (fun x ↦ x + 1) [1, 2, 3] = [2, 3, 4] := by rfl

example : (fun x ↦ x + 1) '' { 1, 2, 3} = { 2, 3, 4} := by
  -- Apply the function to each element of the set.
  ext y
  simp [Set.mem_image];
  -- The equivalence follows from the symmetry of equality.
  simp [eq_comm]