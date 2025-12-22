/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fde2558f-3f9a-45ce-96fa-a941c1e7b1d6

The following was proved by Aristotle:

- theorem padWithO_length (n : Nat) (s : String) : (padWithO n s).length = max n s.length
-/

import Mathlib


def padWithO (n : Nat) (s : String) : String :=
  if s.length ≥ n then
    s
  else
    padWithO n ("o" ++ s)
termination_by n - s.length
decreasing_by
  have : "o".length = 1 := by rfl
  grind [String.length_append]

#eval padWithO 5 "abc"

example : padWithO 5 "abc" = "ooabc" := by
  unfold padWithO
  simp
  rw [show "abc".length = 3 by rfl]
  simp
  unfold padWithO
  simp
  rw [show "oabc".length = 4 by rfl]
  simp
  unfold padWithO
  rw [show "ooabc".length = 5 by rfl]
  simp

noncomputable section AristotleLemmas

theorem padWithO_length (n : Nat) (s : String) : (padWithO n s).length = max n s.length := by
  have h_ind : ∀ n s, (padWithO n s).length = max n s.length := by
    -- We'll use induction on the difference between `n` and `s.length`.
    have h_ind : ∀ k, ∀ n s, s.length + k = n → (padWithO n s).length = max n s.length := by
      intro k;
      induction k
      · unfold padWithO; aesop;
      · aesop
        unfold padWithO
        simp_all
        specialize a (n+1) s
        -- By definition of `padWithO`, we know that it pads the string with 'o's at the beginning until its length is at least `n`. Therefore, the length of the padded string is `n`.
        have h_pad_length : ∀ (n : ℕ) (s : String), (padWithO n s).length = max n s.length := by
          intros n s;
          induction' h : n - s.length using Nat.strong_induction_on with n ih generalizing s;
          unfold padWithO; aesop;
          convert ih ( n_3 - ( s.length + 1 ) ) ( by omega ) ( "o" ++ s ) rfl using 1;
          norm_num [ String.length_append ];
          rw [ max_eq_left h.le, max_eq_left ( by linarith [ show ( "o".length : ℕ ) = 1 by rfl ] ) ];
        aesop;
        exact add_comm ( "o".length ) _ ▸ by simp +arith +decide;
    intro n s; specialize h_ind ( n - s.length ) n s; cases le_total s.length n <;> aesop;
    unfold padWithO; aesop;
  exact h_ind n s

end AristotleLemmas

example (n : Nat) (s : String) (h : n ≥ s.length): (padWithO n s).length = n := by
  rw [ padWithO_length, max_eq_left h ]