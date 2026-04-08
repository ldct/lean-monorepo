import Mathlib

/-
How can we write a fast tactic proof for this?
-/

example : (Finset.range 10).filter IsSquare = {0, 1, 4, 9} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, ⟨m, hm⟩⟩
    have hm3 : m ≤ 3 := by nlinarith
    interval_cases m <;> omega
  · rintro (rfl | rfl | rfl | rfl) <;> refine ⟨by omega, ?_⟩
    · exact ⟨0, by ring⟩
    · exact ⟨1, by ring⟩
    · exact ⟨2, by ring⟩
    · exact ⟨3, by ring⟩
