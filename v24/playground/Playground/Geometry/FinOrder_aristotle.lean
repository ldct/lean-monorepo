/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a371c425-ecb4-4b07-bcad-b0205e089472

The following was proved by Aristotle:

- theorem orderOf_eq {G} [Group G] [Fintype G] [DecidableEq G] (g : G)
: finOrderOf g = orderOf g
-/

import Mathlib


def finOrderOf {G} [Group G] [Fintype G] [DecidableEq G] (a : G) : Fin ((Fintype.card G) + 1):=
  Finset.min' { n : Fin ((Fintype.card G) + 1) | n ≠ 0 ∧ a ^ (n.val) = 1 } (by
    use ⟨ Fintype.card G, by grind ⟩
    simp
  )

#check Subsingleton.orderOf_eq

theorem orderOf_eq {G} [Group G] [Fintype G] [DecidableEq G] (g : G)
: finOrderOf g = orderOf g := by
  have h_finOrderOf_def : finOrderOf g = ⟨orderOf g, by
    exact Nat.lt_succ_of_le ( orderOf_le_card_univ )⟩ := by
    refine le_antisymm ?_ ?_;
    · refine Finset.min'_le _ _ ?_
      simp +decide [ pow_orderOf_eq_one ];
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ orderOf g, orderOf_pos g, pow_orderOf_eq_one g ⟩;
    · unfold finOrderOf
      simp [ Finset.min' ]
      intro b hb hb'
      exact Nat.le_of_dvd ( Fin.pos_iff_ne_zero.2 hb ) ( orderOf_dvd_iff_pow_eq_one.2 hb' )
  exact congr_arg Fin.val h_finOrderOf_def

theorem orderOf1 {G} [Group G] [Fintype G] [DecidableEq G] : finOrderOf (1 : G) = 1 := by
  simp [finOrderOf]
  rw [Finset.min'_eq_iff]
  constructor
  · simp
  intro b hb
  simp at *
  exact Fin.one_le_of_ne_zero hb

def exponent {G} [Group G] [Fintype G] [DecidableEq G] : Fin ((Fintype.card G) + 1) :=
  Finset.max' ( Finset.image (fun (g : G) ↦ finOrderOf g) (Finset.univ : Finset G)) (by
    use ⟨ 1, by grind [Fintype.card_pos] ⟩
    simp
    use 1
    convert orderOf1
    simp
    rw [Nat.mod_eq_of_lt]
    grind [Fintype.card_pos]
  )

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `T`
Unknown identifier `T`-/
#eval Finset.image (fun (g : T) ↦ orderOf g) (Finset.univ : Finset T)

-- #eval { orderOf g | g : T}


#check orderOf
