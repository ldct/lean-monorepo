import Mathlib


set_option linter.style.refine false

set_option linter.style.multiGoal false

-- TODO(v31 port): `IsAddSubmonoid`/`IsAddSubgroup` were removed from Mathlib
-- (deprecated bundled predicates). We reproduce their original definitions here
-- locally to preserve the statements and proofs of this file.
structure IsAddSubmonoid {M : Type*} [AddZeroClass M] (s : Set M) : Prop where
  zero_mem : (0 : M) ∈ s
  add_mem : ∀ {a b}, a ∈ s → b ∈ s → a + b ∈ s

structure IsAddSubgroup {G : Type*} [AddGroup G] (s : Set G) : Prop extends IsAddSubmonoid s where
  neg_mem : ∀ {a}, a ∈ s → -a ∈ s

def TorsionSet (G : Type) [AddGroup G] : Set G :=
{ x | addOrderOf x ≠ 0 }

-- 2.1.6.(a)
example {G : Type} [AddCommGroup G] : IsAddSubgroup (TorsionSet G) := by
  have mem_iff : ∀ x : G, x ∈ TorsionSet G ↔ IsOfFinAddOrder x := by
    intro x; simp only [TorsionSet, Set.mem_setOf_eq, addOrderOf_ne_zero_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_iff]; simpa using (isOfFinAddOrder_iff_nsmul_eq_zero (a := (0 : G))).2 ⟨1, by simp⟩
  · intro a b ha hb
    rw [mem_iff] at ha hb ⊢
    exact ha.add hb
  · intro a ha
    rw [mem_iff] at ha ⊢
    exact ha.neg

-- 2.1.6.(b)
noncomputable section AristotleLemmas

/-
The torsion set of the infinite dihedral group (viewed additively) is not a subgroup.
-/
lemma not_isAddSubgroup_torsionSet_dihedral :
¬ IsAddSubgroup (TorsionSet (Additive (DihedralGroup 0))) := by
  intro h
  -- `sr 0` and `sr 1` both have (additive) order 2, so they lie in the torsion set,
  -- but their sum is `r 1`, which has infinite order in the infinite dihedral group.
  have mem_iff : ∀ x : DihedralGroup 0,
      (Additive.ofMul x) ∈ TorsionSet (Additive (DihedralGroup 0)) ↔ orderOf x ≠ 0 := by
    intro x
    simp only [TorsionSet, Set.mem_setOf_eq, addOrderOf_ofMul_eq_orderOf]
  have hsr0 : (Additive.ofMul (DihedralGroup.sr (0 : ZMod 0))) ∈ TorsionSet (Additive (DihedralGroup 0)) := by
    rw [mem_iff, DihedralGroup.orderOf_sr]; norm_num
  have hsr1 : (Additive.ofMul (DihedralGroup.sr (1 : ZMod 0))) ∈ TorsionSet (Additive (DihedralGroup 0)) := by
    rw [mem_iff, DihedralGroup.orderOf_sr]; norm_num
  have hsum := h.add_mem hsr0 hsr1
  -- `sr 0 + sr 1 = sr 0 * sr 1 = r 1`
  have hval : (Additive.ofMul (DihedralGroup.sr (0 : ZMod 0))) + (Additive.ofMul (DihedralGroup.sr (1 : ZMod 0)))
      = Additive.ofMul (DihedralGroup.r (1 : ZMod 0)) := by
    rw [← ofMul_mul, DihedralGroup.sr_mul_sr]; norm_num
  rw [hval, mem_iff] at hsum
  exact hsum DihedralGroup.orderOf_r_one

end AristotleLemmas

example : ∃ (G : Type) (inst : AddGroup G) (H : Set G)
, ¬ IsAddSubgroup (TorsionSet G) := by
  -- We use the infinite dihedral group `DihedralGroup 0`, viewed additively via `Additive`.
  use Additive (DihedralGroup 0);
  exact ⟨ inferInstance, Set.univ, not_isAddSubgroup_torsionSet_dihedral ⟩