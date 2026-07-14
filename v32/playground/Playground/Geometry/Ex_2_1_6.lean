import Playground.Geometry.Chapter_2_1

set_option linter.style.refine false
set_option linter.style.multiGoal false


namespace Ex_2_1_6
open Chapter_2_1

def TorsionSet (G : Type) [AddGroup G] : Set G :=
{ x | addOrderOf x ≠ 0 }

-- 2.1.6.(a)
example {G : Type} [AddCommGroup G] : IsAddSubgroup (TorsionSet G) := by
  sorry

-- 2.1.6.(b)

/-
The torsion set of the infinite dihedral group (viewed additively) is not a subgroup.
-/
lemma not_isAddSubgroup_torsionSet_dihedral :
¬ IsAddSubgroup (TorsionSet (Additive (DihedralGroup 0))) := by
  unfold IsAddSubgroup TorsionSet
  generalize_proofs at *; (
  simp +zetaDelta at *;
  rintro -;
  refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num [ IsOfFinAddOrder ];
  exact DihedralGroup.sr 0
  generalize_proofs at *; (
  use 2; simp +decide ;);
  exact DihedralGroup.sr 1
  generalize_proofs at *; (
  use 2; simp +decide ;);
  simp +decide [ Function.periodicPts ];
  intro x hx h
  replace h := congr_arg ( fun f => f.toMul ) h
  simp_all +decide
  injection h with h
  aesop)

example : ∃ (G : Type) (_ : AddGroup G)
, ¬ IsAddSubgroup (TorsionSet G) := by
  -- We use the infinite dihedral group `DihedralGroup 0`, viewed additively via `Additive`.
  use Additive (DihedralGroup 0);
  exact ⟨ inferInstance, not_isAddSubgroup_torsionSet_dihedral ⟩


end Ex_2_1_6