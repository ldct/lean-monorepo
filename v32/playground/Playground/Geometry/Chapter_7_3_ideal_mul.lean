import Mathlib

open Pointwise

-- Ideal R is definitionally Submodule R R.
-- Mathlib's Submodule.mul_def requires CommSemiring, but for ideals
-- we can prove the same result with just Semiring (noncommutative rings).
