
namespace IdealSumCarrier_aristotle

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3c0bf043-245a-4e01-a6c7-2feaa892df6f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example {R} [Ring R] (I J : Ideal R)
: (I + J).carrier = {i + j | (i ∈ I.carrier) (j ∈ J.carrier) }
-/

import Mathlib


example {R} [Ring R] (I J : Ideal R)
: (I + J).carrier = {i + j | (i ∈ I.carrier) (j ∈ J.carrier) } := by
  -- By definition of sum of ideals, we have $(I + J).carrier = \{x \in R \mid \exists i \in I, \exists j \in J, i + j = x\}$.
  ext x
  simp [Submodule.mem_sup]

end IdealSumCarrier_aristotle