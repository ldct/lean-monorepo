import Mathlib.Tactic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations

-- Test with 'use' and type ascription
example : ∀ (R : Type*) [CommRing R], ∃ (A B : Type*) (_ : Ring A) (_ : Ring B), True := by
  intro R _
  use (R : Type _)
  use (R : Type _)
  exact ⟨inferInstance, inferInstance, trivial⟩

-- Test with refine
example : ∀ (R : Type*) [CommRing R], ∃ (A B : Type*) (_ : Ring A) (_ : Ring B), True := by
  intro R _
  refine ⟨R, R, inferInstance, inferInstance, trivial⟩
