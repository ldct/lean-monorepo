/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5150505f-4d7b-4af4-8352-b4299605eced

The following was proved by Aristotle:

- lemma idlem (g : SO3) :  (cpoly g).roots.count 1 = 3 → g = 1
-/

import Mathlib

set_option maxHeartbeats 0
set_option linter.style.longLine false

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

abbrev MAT:= Matrix (Fin 3) (Fin 3) ℝ

noncomputable def as_complex (M : MAT) : Matrix (Fin 3) (Fin 3) ℂ := (algebraMap ℝ ℂ).mapMatrix M

noncomputable def cpoly (g : SO3) := Matrix.charpoly (as_complex g.val)

lemma idlem (g : SO3) :  (cpoly g).roots.count 1 = 3 → g = 1 := by
  -- Since the only real roots of $P_g$ are $\pm 1$, and $P_g$ has three roots, they must all be $1$. Hence, $g$ is the identity matrix.
  have h_roots : (Matrix.charpoly (as_complex g.val)).roots = {1, 1, 1} → g = 1 := by
    have h_roots : (Matrix.charpoly (as_complex g.val)).roots = {1, 1, 1} → Matrix.charpoly (as_complex g.val) = (Polynomial.X - Polynomial.C 1) ^ 3 := by
      intro h_roots
      have h_poly : (Matrix.charpoly (as_complex g.val)).roots = {1, 1, 1} := by
        exact h_roots;
      rw [ ← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq ( show Polynomial.Monic ( Matrix.charpoly ( as_complex g.val ) ) from ?_ ) ];
      · norm_num [ h_poly ];
        ring;
      · aesop;
      · exact Matrix.charpoly_monic _;
    intro h; specialize h_roots h; simp_all +decide [ Matrix.charpoly, Matrix.det_fin_three ] ;
    -- By comparing coefficients, we can see that $g$ must be the identity matrix.
    have h_coeff : ∀ i j, (g.val i j : ℂ) = if i = j then 1 else 0 := by
      -- By comparing coefficients of $X^2$ on both sides of the equation, we can derive that the sum of the diagonal elements of $g$ must be 3.
      have h_diag_sum : (g.val 0 0 : ℂ) + (g.val 1 1 : ℂ) + (g.val 2 2 : ℂ) = 3 := by
        have h₁ := congr_arg ( Polynomial.eval 0 ) h_roots; have h₂ := congr_arg ( Polynomial.eval 1 ) h_roots; have h₃ := congr_arg ( Polynomial.eval ( -1 ) ) h_roots; norm_num [ Complex.ext_iff ] at *; linarith!;
      -- Since $g$ is orthogonal, we have $g^T g = I$.
      have h_orthogonal : (g.val.transpose * g.val : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
        have := g.2.1; simp_all +decide [ Matrix.mul_eq_one_comm ] ;
        exact this.2;
      -- Since $g$ is orthogonal, we have $g^T g = I$. Therefore, the sum of the squares of the entries in each row is 1.
      have h_row_squares : ∀ i, (g.val i 0 : ℝ)^2 + (g.val i 1 : ℝ)^2 + (g.val i 2 : ℝ)^2 = 1 := by
        intro i; have := congr_fun ( congr_fun h_orthogonal i ) i; simp_all +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ;
        have := congr_fun ( congr_fun ( show ( g.val * g.val.transpose : Matrix ( Fin 3 ) ( Fin 3 ) ℝ ) = 1 from by simpa [ Matrix.mul_eq_one_comm ] using h_orthogonal ) i ) i; simp_all +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ; ring_nf at *; aesop;
      -- Since the sum of the squares of the entries in each row is 1 and the sum of the diagonal elements is 3, each diagonal element must be 1.
      have h_diag_one : ∀ i, (g.val i i : ℝ) = 1 := by
        norm_cast at *; simp_all +decide [ Fin.forall_fin_succ ] ;
        refine' ⟨ _, _, _ ⟩ <;> nlinarith only [ h_diag_sum, h_row_squares, sq_nonneg ( ( g.val 0 0 : ℝ ) - 1 ), sq_nonneg ( ( g.val 1 1 : ℝ ) - 1 ), sq_nonneg ( ( g.val 2 2 : ℝ ) - 1 ) ];
      simp_all +decide [ Fin.forall_fin_succ ];
      exact ⟨ ⟨ by nlinarith only [ h_row_squares.1 ], by nlinarith only [ h_row_squares.1 ] ⟩, ⟨ by nlinarith only [ h_row_squares.2.1 ], by nlinarith only [ h_row_squares.2.1 ] ⟩, by nlinarith only [ h_row_squares.2.2 ], by nlinarith only [ h_row_squares.2.2 ] ⟩;
    ext i j; specialize h_coeff i j; aesop;
  -- Since the polynomial is of degree 3, if 1 is a root with multiplicity 3, then the polynomial must be $(x-1)^3$.
  have h_poly_form : (Matrix.charpoly (as_complex g.val)).roots = {1, 1, 1} ↔ Multiset.count 1 (Matrix.charpoly (as_complex g.val)).roots = 3 := by
    have h_poly_form : (Matrix.charpoly (as_complex g.val)).degree = 3 := by
      simp +decide [ Matrix.charpoly_degree_eq_dim ];
    -- Since the polynomial is of degree 3, if 1 is a root with multiplicity 3, then the polynomial must be $(x-1)^3$. Hence, the roots must be exactly {1, 1, 1}.
    have h_poly_form : (Matrix.charpoly (as_complex g.val)).roots = {1, 1, 1} ↔ Multiset.count 1 (Matrix.charpoly (as_complex g.val)).roots = 3 := by
      have h_poly_form : (Matrix.charpoly (as_complex g.val)).roots = {1, 1, 1} → Multiset.count 1 (Matrix.charpoly (as_complex g.val)).roots = 3 := by
        aesop
      have h_poly_form' : Multiset.count 1 (Matrix.charpoly (as_complex g.val)).roots = 3 → (Matrix.charpoly (as_complex g.val)).roots = {1, 1, 1} := by
        intro h_count
        have h_poly_form' : Multiset.card (Matrix.charpoly (as_complex g.val)).roots = 3 := by
          have h_poly_form' : Multiset.card (Matrix.charpoly (as_complex g.val)).roots ≤ 3 := by
            exact le_trans ( Polynomial.card_roots' _ ) ( Polynomial.natDegree_le_of_degree_le <| le_of_eq ‹_› );
          exact le_antisymm h_poly_form' ( by linarith [ Multiset.count_le_card 1 ( Matrix.charpoly ( as_complex g.val ) |> Polynomial.roots ) ] );
        have h_poly_form' : ∀ x ∈ (Matrix.charpoly (as_complex g.val)).roots, x = 1 := by
          intro x hx; contrapose! h_count; simp_all +decide ;
          have h_poly_form' : Polynomial.rootMultiplicity 1 (Matrix.charpoly (as_complex g.val)) + Polynomial.rootMultiplicity x (Matrix.charpoly (as_complex g.val)) ≤ 3 := by
            have h_poly_form' : Polynomial.rootMultiplicity 1 (Matrix.charpoly (as_complex g.val)) + Polynomial.rootMultiplicity x (Matrix.charpoly (as_complex g.val)) ≤ Multiset.card (Matrix.charpoly (as_complex g.val)).roots := by
              have h_poly_form' : Polynomial.rootMultiplicity 1 (Matrix.charpoly (as_complex g.val)) + Polynomial.rootMultiplicity x (Matrix.charpoly (as_complex g.val)) ≤ Multiset.card (Multiset.filter (fun y => y = 1) (Matrix.charpoly (as_complex g.val)).roots) + Multiset.card (Multiset.filter (fun y => y = x) (Matrix.charpoly (as_complex g.val)).roots) := by
                rw [ Multiset.filter_eq', Multiset.filter_eq' ] ; aesop;
              refine le_trans h_poly_form' ?_;
              rw [ ← Multiset.card_add ] ; exact Multiset.card_le_card <| Multiset.le_iff_count.mpr fun y => by by_cases hy : y = 1 <;> by_cases hy' : y = x <;> aesop;
            linarith;
          linarith [ show Polynomial.rootMultiplicity x ( Matrix.charpoly ( as_complex g.val ) ) > 0 from Nat.pos_of_ne_zero ( by aesop ) ];
        exact Multiset.eq_replicate.mpr ⟨ by assumption, h_poly_form' ⟩
      exact ⟨h_poly_form, h_poly_form'⟩;
    exact h_poly_form;
  exact fun h => h_roots <| h_poly_form.mpr h
