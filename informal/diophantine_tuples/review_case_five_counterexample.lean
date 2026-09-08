-- Review counterexample to the published Case V statement as of 2026-09-07.
-- Uses the Prove2me workspace definition; run with its lake environment.
import Definitions.Def_diophantine_descent
open DiophantineDescent

private theorem t8 : Triple 1 3 8 :=
  ⟨by decide, by decide, by decide, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨5, rfl⟩⟩
private theorem t120 : Triple 1 3 120 :=
  ⟨by decide, by decide, by decide, ⟨2, rfl⟩, ⟨11, rfl⟩, ⟨19, rfl⟩⟩
private theorem t1680 : Triple 1 3 1680 :=
  ⟨by decide, by decide, by decide, ⟨2, rfl⟩, ⟨41, rfl⟩, ⟨71, rfl⟩⟩
private theorem step120 : Step 1 3 120 1 3 8 := by
  refine ⟨t120, ?_, t8, 2, 11, 19, 8, rfl, rfl, rfl, rfl, by decide, by decide, List.Perm.refl _⟩
  rintro ⟨r, hr, hc⟩
  have he : r = 58 := by omega
  subst r
  exact (by decide : ¬ (1 * 3 + 1 = 58 ^ 2)) hr
private theorem step1680 : Step 1 3 1680 1 3 120 := by
  refine ⟨t1680, ?_, t120, 2, 41, 71, 120, rfl, rfl, rfl, rfl, by decide, by decide, List.Perm.refl _⟩
  rintro ⟨r, hr, hc⟩
  have he : r = 838 := by omega
  subst r
  exact (by decide : ¬ (1 * 3 + 1 = 838 ^ 2)) hr

theorem case_five_counterexample :
    Triple 1 3 1680 ∧ HasDegree 1 3 1680 2 ∧
    1 * 1680 < 67700000000000000000000000 ∧
    4 * 1 ^ 2 * 3 ^ 3 < 1680 ∧ 1 * 1680 * 20 < 3609 * 3 ^ 3 := by
  refine ⟨t1680, ?_, by decide, by decide, by decide⟩
  exact HasDegree.succ step1680 (HasDegree.succ step120 (HasDegree.zero t8 ⟨2, rfl, rfl⟩))
