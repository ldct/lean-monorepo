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
    | nil => grind
    | cons y ys ih =>
      grind
  show (xs.foldl (fun acc x => acc ++ [acc.getLast! + x]) [0]).length = xs.length + 1
  grind

lemma prefixSum_eq_scanl (xs : List ℕ) :
    prefixSum xs = List.scanl (· + ·) 0 xs := by
  simp only [prefixSum]
  have key : ∀ (ys : List ℕ) (s : ℕ) (pre : List ℕ),
      ys.foldl (fun acc x => acc ++ [acc.getLast! + x]) (pre ++ [s]) =
      pre ++ List.scanl (· + ·) s ys := by
    intro ys
    induction ys with
    | nil => intro s pre; simp
    | cons y ys ih =>
      intro s pre
      simp only [List.foldl_cons, List.scanl_cons]
      have hlast : (pre ++ [s]).getLast! = s := by simp
      rw [hlast, ih (s + y) (pre ++ [s])]
      simp [List.append_assoc]
  have := key xs 0 []
  simpa using this

lemma prefixSum_getElem (xs : List ℕ) (i : ℕ) (hi : i ≤ xs.length) :
    (prefixSum xs)[i]! = (xs.take i).sum := by
  rw [prefixSum_eq_scanl, getElem!_pos _ _ (by rw [List.length_scanl]; omega),
      List.getElem_scanl, ← List.sum_eq_foldl]

lemma list_sum_take_sub (l : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    (l.take b).sum - (l.take a).sum = (l.drop a |>.take (b - a)).sum := by
  have split : l.take b = l.take a ++ (l.drop a).take (b - a) := by
    conv_lhs => rw [← List.take_append_drop a (l.take b)]
    congr 1
    · rw [List.take_take, min_eq_left hab]
    · rw [List.drop_take]
  rw [split, List.sum_append]
  omega

theorem rangeSum_correct (xs : List ℕ) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ xs.length) :
    ⟪rangeSum a b (prefixSum xs)⟫ = rangeSumNaive a b xs := by
  simp only [rangeSum, rangeSumNaive]
  rw [prefixSum_getElem xs b hb, prefixSum_getElem xs a (Nat.le_trans hab hb)]
  exact list_sum_take_sub xs a b hab

#eval prefixSum [1, 2, 3, 4, 5]
#eval prefixSumLinear [1, 1, 1, 1, 1]
