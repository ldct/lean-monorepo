import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

def prefixSum (xs : List ℕ) : List ℕ :=
  xs.foldl (fun acc x => acc ++ [acc.getLast! + x]) [0]

def prefixSumAcc (xs : List ℕ) (i : ℕ) (acc : ℕ) (result : List ℕ) : TimeM (List ℕ) :=
  if h : i < xs.length then do
    ✓ let newAcc := acc + xs[i]
    prefixSumAcc xs (i + 1) newAcc (result ++ [acc])
  else
    return result ++ [acc]
termination_by xs.length - i

def prefixSumLinear (xs : List ℕ) : TimeM (List ℕ) := prefixSumAcc xs 0 0 []

def rangeSum (a b : ℕ) (ps : List ℕ) : TimeM ℕ := return (ps[b]! - ps[a]!)

-- naive implementation of sum(xs[a:b])
def rangeSumNaive (a b : ℕ) (xs : List ℕ) : ℕ :=
  (xs.drop a |>.take (b - a)).sum

-- correctness

lemma prefixSum_length (xs : List ℕ) : (prefixSum xs).length = xs.length + 1 := by
  have h : ∀ (ys : List ℕ) (init : List ℕ),
      (ys.foldl (fun acc x => acc ++ [acc.getLast! + x]) init).length = init.length + ys.length := by
    intro ys
    induction ys with
    | nil => intro init; simp
    | cons y ys ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih]
      simp [List.length_append]
      omega
  show (xs.foldl (fun acc x => acc ++ [acc.getLast! + x]) [0]).length = xs.length + 1
  rw [h]; simp; omega

lemma prefixSum_getElem (xs : List ℕ) (i : ℕ) (hi : i ≤ xs.length) :
    (prefixSum xs)[i]! = (xs.take i).sum := by
  sorry

lemma list_sum_take_sub (l : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    (l.take b).sum - (l.take a).sum = (l.drop a |>.take (b - a)).sum := by
  sorry

theorem rangeSum_correct (xs : List ℕ) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ xs.length) :
    ⟪rangeSum a b (prefixSum xs)⟫ = rangeSumNaive a b xs := by
  simp only [rangeSum, rangeSumNaive]
  rw [prefixSum_getElem xs b hb, prefixSum_getElem xs a (Nat.le_trans hab hb)]
  exact list_sum_take_sub xs a b hab

#eval prefixSum [1, 2, 3, 4, 5]
#eval prefixSumLinear [1, 1, 1, 1, 1]
