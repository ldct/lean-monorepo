/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- theorem my_favorite_theorem (k : ℕ) :
  ∑' n : ℕ+, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 / k
-/

import Mathlib


theorem binom_inv_telescope (n k : ℕ) (hk : 0 < k) :
    1 / (Nat.choose (n + k + 1) n) =
      (k + 1 : ℚ) / k *
        (1 / (Nat.choose (n + k) n : ℚ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℚ)) := by
  field_simp [Nat.cast_choose];
  rw [ Nat.cast_choose ] <;> norm_num [ Nat.factorial, add_assoc ] ; ring;
  -- Let's simplify the expression by factoring out common terms.
  field_simp
  ring_nf at *

open Real

open scoped BigOperators

theorem my_favorite_theorem (k : ℕ) :
  ∑' n : ℕ+, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 / k := by
    -- Rewrite each term using `binom_inv_telescope`. The sum telescopes.
    by_cases hk : k = 0 <;> simp_all +decide [ Nat.succ_div ];
    · -- The sum of the reciprocals of (n+1) over all positive integers n is the harmonic series shifted by one, which is known to diverge. Therefore, the sum is infinite, not zero.
      have h_harmonic : ¬ Summable (fun n : ℕ+ => (1 : ℝ) / (n + 1)) := by
        norm_num +zetaDelta at *;
        exact fun h => absurd ( h.comp_injective <| show Function.Injective ( fun k : ℕ ↦ ⟨ k + 1, Nat.succ_pos k ⟩ : ℕ → ℕ+ ) from fun a b h ↦ by simpa using congr_arg PNat.val h ) <| by exact_mod_cast mt ( fun s ↦ summable_nat_add_iff 2 |>.1 s ) Real.not_summable_natCast_inv;
      rw [ tsum_eq_zero_of_not_summable ] ; aesop;
    · -- We'll use the identity $\frac{1}{\binom{n+k+1}{n}} = \frac{k+1}{k} \left( \frac{1}{\binom{n+k}{n}} - \frac{1}{\binom{n+k+1}{n+1}} \right)$ to rewrite the sum.
      have h_identity : ∀ n : ℕ+, (1 / (Nat.choose (n + k + 1) n : ℝ)) = (k + 1) / k * (1 / (Nat.choose (n + k) n : ℝ) - 1 / (Nat.choose (n + k + 1) (n + 1) : ℝ)) := by
        intro n; rw [ Nat.cast_choose, Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
        simp +decide [ Nat.factorial, Nat.succ_sub, field_simps, hk ];
        -- Combine and simplify the fractions on the right-hand side.
        field_simp
        ring;
      -- Let's rewrite the sum using the identity.
      have h_sum_identity : ∀ N : ℕ+, ∑ n in Finset.Icc 1 N, (1 / (Nat.choose (n + k + 1) n : ℝ)) = (k + 1) / k * (1 / (Nat.choose (k + 1) 1 : ℝ) - 1 / (Nat.choose (N + k + 1) (N + 1) : ℝ)) := by
        intro N
        induction' N using PNat.recOn with N ih;
        · aesop;
          exact Or.inl <| add_comm _ _;
        · erw [ Finset.sum_eq_sum_diff_singleton_add ( show N + 1 ∈ Finset.Icc 1 ( N + 1 ) from Finset.mem_Icc.mpr ⟨ Nat.le_add_left _ _, Nat.le_refl _ ⟩ ), h_identity ];
          rw [ show ( Finset.Icc 1 ( N + 1 ) \ { N + 1 } ) = Finset.Icc 1 N by ( rw [ Finset.sdiff_singleton_eq_erase ] ; aesop ) ] ; aesop ; ring;
      -- Let's take the limit of the partial sum as $N$ approaches infinity.
      have h_limit : Filter.Tendsto (fun N : ℕ+ => ∑ n in Finset.Icc 1 N, (1 / (Nat.choose (n + k + 1) n : ℝ))) Filter.atTop (nhds ((k + 1) / k * (1 / (Nat.choose (k + 1) 1 : ℝ) - 0))) := by
        -- Since $\frac{1}{\binom{N+k+1}{N+1}}$ tends to $0$ as $N$ approaches infinity, we can use the fact that the limit of a product is the product of the limits.
        have h_limit_zero : Filter.Tendsto (fun N : ℕ+ => 1 / (Nat.choose (N + k + 1) (N + 1) : ℝ)) Filter.atTop (nhds 0) := by
          refine' tendsto_const_nhds.div_atTop _;
          refine' Filter.tendsto_atTop_mono _ ( Filter.tendsto_atTop_atTop.mpr _ );
          rotate_left;
          use fun n => n + 1;
          · exact fun x => ⟨ ⟨ ⌈x⌉₊ + 1, Nat.succ_pos _ ⟩, fun n hn => by linarith [ Nat.le_ceil x, show ( n : ℝ ) ≥ ⌈x⌉₊ + 1 by exact_mod_cast hn ] ⟩;
          · intro n; norm_cast; induction' n using PNat.recOn with n IH <;> norm_num [ Nat.choose ] at *;
            · linarith [ Nat.pos_of_ne_zero hk, Nat.choose_pos ( show 2 ≤ 1 + k from by linarith [ Nat.pos_of_ne_zero hk ] ) ];
            · simp +arith +decide [ Nat.choose_succ_succ ] at *;
              linarith [ Nat.choose_pos ( show ( n : ℕ ) + 1 ≤ k + n by linarith [ PNat.pos n, Nat.pos_of_ne_zero hk ] ) ];
        simpa only [ h_sum_identity ] using tendsto_const_nhds.mul ( tendsto_const_nhds.sub h_limit_zero );
      -- Since the partial sums converge to $1/k$, and the series is absolutely convergent, the infinite sum must also be $1/k$.
      have h_infinite_sum : Filter.Tendsto (fun N : ℕ+ => ∑ n in Finset.range N, (1 / (Nat.choose (n + k + 2) (n + 1) : ℝ))) Filter.atTop (nhds (1 / k)) := by
        convert h_limit using 2 <;> norm_num;
        · refine' Finset.sum_bij ( fun x hx => ⟨ x + 1, Nat.succ_pos x ⟩ ) _ _ _ _ <;> aesop;
          · simpa using congr_arg Subtype.val a;
          · induction b using PNat.recOn <;> aesop;
          · ring;
        · field_simp;
      have h_infinite_sum : Filter.Tendsto (fun N : ℕ => ∑ n in Finset.range N, (1 / (Nat.choose (n + k + 2) (n + 1) : ℝ))) Filter.atTop (nhds (1 / k)) := by
        rw [ Filter.tendsto_atTop' ] at *;
        exact fun s hs => by obtain ⟨ a, ha ⟩ := h_infinite_sum s hs; exact ⟨ a, fun n hn => ha ⟨ n, Nat.pos_of_ne_zero fun h => by subst h; norm_num at hn ⟩ hn ⟩ ;
      convert tendsto_nhds_unique ( Summable.hasSum ( show Summable _ from by exact ( by { by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_infinite_sum ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h } ) ) |> HasSum.tendsto_sum_nat ) h_infinite_sum using 1 ; aesop;
      · rw [ ← Equiv.tsum_eq ( Equiv.pnatEquivNat.symm ) ] ; aesop;
        exact tsum_congr fun n => by have := h_identity ⟨ n + 1, Nat.succ_pos n ⟩ ; norm_num [ add_comm, add_left_comm, add_assoc ] at * ; linarith;
      · ring
