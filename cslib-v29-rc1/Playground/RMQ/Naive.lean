import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.List.MinMax
import Mathlib.Order.WithBot
import Playground.RMQ.SparseTable

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-
# Naive RMQ

The naive approach to Range Minimum Query:
- Preprocessing: O(1) — just store the array
- Query: O(n) — linear scan over the query range

Cost model: count `min` comparisons (same as SparseTable).
-/

structure NaiveRMQ where
  data : Array ℕ

/-- Store the array with no preprocessing. Time: 0. -/
def NaiveRMQ.make (a : Array ℕ) : TimeM NaiveRMQ := pure { data := a }

/-- Compute `min(a[l], a[l+1], ..., a[l+n])` with `n` min-comparisons. -/
private def naiveScan (a : Array ℕ) (l n: ℕ) : TimeM ℕ := do match n with
  | 0 => return a[l]!
  | n + 1 =>
    let prev ← naiveScan a l n
    ✓ return (min prev a[l + n + 1]!)

/-- Query the minimum of `a[l..r]` by linear scan (clamped to array bounds). -/
def NaiveRMQ.query (st : NaiveRMQ) (l r : ℕ) : TimeM ℕ :=
  naiveScan st.data l (min r (st.data.size - 1) - l)

/-
# Time complexity
-/

@[simp] private lemma naiveScan_time (a : Array ℕ) (l : ℕ) :
    ∀ n, (naiveScan a l n).time = n
  | 0 => by simp [naiveScan]
  | n + 1 => by simp [naiveScan, naiveScan_time a l n]

/-- Preprocessing costs 0 (just stores the array). -/
theorem NaiveRMQ.make_time (a : Array ℕ) :
    (NaiveRMQ.make a).time = 0 := by
  simp [NaiveRMQ.make]

/-- A query over `[l, r]` costs at most `|a|` min-comparisons. -/
theorem NaiveRMQ.query_time_le (a : Array ℕ) (l r : ℕ) :
    (NaiveRMQ.query ⟪NaiveRMQ.make a⟫ l r).time ≤ a.size := by
  simp [NaiveRMQ.query, NaiveRMQ.make]
  omega

/-
# Correctness
-/

private lemma rangeMin_one' (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    rangeMin xs j 1 = xs[j] := by
  grind [List.drop_eq_getElem_cons, List.take_add_one, List.minimum_singleton, rangeMin]

private lemma rmqNaive_eq_rangeMin' (vals : Array ℕ) (l r : ℕ) :
    rmqNaive vals l r = rangeMin vals.toList l (r - l + 1) := by
  grind [rmqNaive, rangeMin, Array.toList_extract]

private lemma naiveScan_correct (a : Array ℕ) (l : ℕ) :
    ∀ n, l + n < a.size →
    (⟪naiveScan a l n⟫ : WithTop ℕ) = rangeMin a.toList l (n + 1)
  | 0, h => by
    simp [naiveScan, getElem!_pos a l (by omega)]
    exact (rangeMin_one' a.toList l (by simp; omega)).symm
  | n + 1, h => by
    have ih := naiveScan_correct a l n (by omega)
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl,
        rangeMin_split a.toList l (n + 1) 1,
        rangeMin_one' a.toList (l + (n + 1)) (by simp; omega)]
    grind [naiveScan, WithTop.coe_min]

theorem NaiveRMQ.correct (a : Array ℕ) (l r : ℕ) (h : l ≤ r) (hr : r < a.size) :
    ⟪NaiveRMQ.query ⟪NaiveRMQ.make a⟫ l r⟫ = rmqNaive a l r := by
  simp only [NaiveRMQ.query, NaiveRMQ.make, ret_pure]
  have : min r (a.size - 1) = r := by omega
  rw [this, rmqNaive_eq_rangeMin']
  exact naiveScan_correct a l (r - l) (by omega)

/-
# RMQSolution instance
-/

instance : RMQSolution NaiveRMQ where
  make := NaiveRMQ.make
  query := NaiveRMQ.query
  correct := NaiveRMQ.correct
  make_time _ := 0
  make_time_bound := by intro a; simp [NaiveRMQ.make_time]
  query_time n := n
  query_time_bound := by intro a l r; exact NaiveRMQ.query_time_le a l r

end Cslib.Algorithms.Lean.TimeM
