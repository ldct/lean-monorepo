import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Basic

-- Test universe unification for localization existential
theorem test_loc (R : Type*) [CommRing R] [IsDomain R] (S : Submonoid R) :
    ∃ (L : Type*) (_ : CommRing L) (_ : Algebra R L), IsLocalization S L := by
  exact ⟨Localization S, inferInstance, inferInstance, inferInstance⟩
