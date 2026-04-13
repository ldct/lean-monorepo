import Mathlib.Tactic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

-- Test 1: Can we bridge the EuclideanDomain → PID diamond?
theorem test_ed_pid (R : Type*) [CommRing R] [IsDomain R] [EuclideanDomain R] :
    IsPrincipalIdealRing R := by
  constructor
  intro S
  have h := @EuclideanDomain.to_principal_ideal_domain R _
  exact h.principal S

-- Test 2: Does UFD imply IsDomain without Nontrivial?
-- theorem test_ufd_id (R : Type*) [CommRing R] [UniqueFactorizationMonoid R] : IsDomain R := by
--   infer_instance
