import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.List.MinMax
import Mathlib.Order.WithBot
import Playground.RMQ.Basic

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-
# Precomputed RMQ

Precompute all O(n²) answers using dynamic programming:
- Preprocessing: O(n²) — build table where `table[l][k] = min(a[l..l+k])`
- Query: O(1) — single table lookup

Cost model: count `min` comparisons (same as SparseTable).
-/

structure PrecomputedRMQ where
  table : Array (Array ℕ)

/-- The minimum of `a[l], a[l+1], ..., a[l+k]` (pure, no cost tracking). -/
private def rowMinVal (a : Array ℕ) (l : ℕ) : ℕ → ℕ
  | 0 => a[l]!
  | k + 1 => min (rowMinVal a l k) a[l + k + 1]!

/-- Build one row: entry `i` is `min(a[l], ..., a[l+i])`.
    Time: `k` min-comparisons for `k+1` entries. -/
private def buildRow (a : Array ℕ) (l i: ℕ) : TimeM (Array ℕ) := match i with
  | 0 => return #[a[l]!]
  | k + 1 => do
    let row ← buildRow a l k
    ✓ return (row.push (min row.back! a[l + k + 1]!))

/-- Build the first `m` rows of the lookup table. -/
private def buildAllRows (a : Array ℕ) : ℕ → TimeM (Array (Array ℕ))
  | 0 => pure #[]
  | m + 1 => do
    let tbl ← buildAllRows a m
    let row ← buildRow a m (a.size - 1 - m)
    pure (tbl.push row)

/-- Precompute the full lookup table. -/
def PrecomputedRMQ.make (a : Array ℕ) : TimeM PrecomputedRMQ := do
  let tbl ← buildAllRows a a.size
  return { table := tbl }

/-- Look up the precomputed answer. -/
def PrecomputedRMQ.query (st : PrecomputedRMQ) (l r : ℕ) : TimeM ℕ :=
  return st.table[l]![r - l]!

/-
# Size lemmas
-/

@[simp] private lemma buildRow_size (a : Array ℕ) (l : ℕ) :
    ∀ k, ⟪buildRow a l k⟫.size = k + 1
  | 0 => by simp [buildRow]
  | k + 1 => by simp [buildRow, buildRow_size a l k]

@[simp] private lemma buildAllRows_size (a : Array ℕ) :
    ∀ m, ⟪buildAllRows a m⟫.size = m
  | 0 => by simp [buildAllRows]
  | m + 1 => by simp [buildAllRows, buildAllRows_size a m]

/-
# Time complexity
-/

@[simp] private lemma buildRow_time (a : Array ℕ) (l : ℕ) :
    ∀ k, (buildRow a l k).time = k
  | 0 => by simp [buildRow]
  | k + 1 => by simp [buildRow, buildRow_time a l k]

private lemma buildAllRows_time (a : Array ℕ) :
    ∀ m, m ≤ a.size → (buildAllRows a m).time ≤ m * a.size
  | 0, _ => by simp [buildAllRows]
  | m + 1, hm => by
    simp only [buildAllRows, time_bind, time_pure, buildRow_time]
    have ih := buildAllRows_time a m (by omega)
    rw [Nat.succ_mul]; omega

/-- Preprocessing costs at most n² min-comparisons. -/
theorem PrecomputedRMQ.make_time (a : Array ℕ) :
    (PrecomputedRMQ.make a).time ≤ a.size * a.size := by
  simp only [PrecomputedRMQ.make, time_bind, time_pure]
  exact buildAllRows_time a a.size le_rfl

/-- A query costs 0 min-comparisons (just a table lookup). -/
theorem PrecomputedRMQ.query_time (st : PrecomputedRMQ) (l r : ℕ) :
    (PrecomputedRMQ.query st l r).time = 0 := by
  simp [PrecomputedRMQ.query]

/-
# Correctness
-/

private lemma rangeMin_one' (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    rangeMin xs j 1 = xs[j] := by
  grind [List.drop_eq_getElem_cons, List.take_add_one, List.minimum_singleton, rangeMin]

private lemma rmqNaive_eq_rangeMin' (vals : Array ℕ) (l r : ℕ) :
    rmqNaive vals l r = rangeMin vals.toList l (r - l + 1) := by
  grind [rmqNaive, rangeMin, Array.toList_extract]

/-- `rowMinVal` computes the range minimum. -/
private lemma rowMinVal_eq_rangeMin (a : Array ℕ) (l : ℕ) :
    ∀ k, l + k < a.size →
    (rowMinVal a l k : WithTop ℕ) = rangeMin a.toList l (k + 1)
  | 0, h => by
    simp [rowMinVal, getElem!_pos a l (by omega)]
    exact (rangeMin_one' a.toList l (by simp; omega)).symm
  | k + 1, h => by
    have ih := rowMinVal_eq_rangeMin a l k (by omega)
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl,
        rangeMin_split a.toList l (k + 1) 1,
        rangeMin_one' a.toList (l + (k + 1)) (by simp; omega)]
    grind [rowMinVal, WithTop.coe_min]

/-- Each entry of `buildRow` matches `rowMinVal`. -/
private lemma buildRow_getElem (a : Array ℕ) (l k i : ℕ) (hi : i ≤ k) :
    ⟪buildRow a l k⟫[i]'(by rw [buildRow_size]; omega) = rowMinVal a l i := by
  induction k generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp [buildRow, rowMinVal]
  | succ k ih =>
    simp only [buildRow, ret_bind, ret_pure]
    by_cases hik : i ≤ k
    · rw [Array.getElem_push_lt (by rw [buildRow_size]; omega)]
      exact ih i hik
    · obtain rfl : i = k + 1 := by omega
      have hsz : ⟪buildRow a l k⟫.size = k + 1 := buildRow_size a l k
      have hback : ⟪buildRow a l k⟫.back! = rowMinVal a l k := by
        show ⟪buildRow a l k⟫[⟪buildRow a l k⟫.size - 1]! = rowMinVal a l k
        rw [hsz, getElem!_pos _ _ (by omega)]
        exact ih k (by omega)
      simp [Array.getElem_push, buildRow_size, rowMinVal, hback]

/-- The rows of `buildAllRows` match `buildRow`. -/
private lemma buildAllRows_getElem (a : Array ℕ) (m l : ℕ) (hl : l < m) (hm : m ≤ a.size) :
    ⟪buildAllRows a m⟫[l]'(by rw [buildAllRows_size]; omega) = ⟪buildRow a l (a.size - 1 - l)⟫ := by
  induction m generalizing l with
  | zero => omega
  | succ m ih =>
    simp only [buildAllRows, ret_bind, ret_pure]
    by_cases hlm : l < m
    · rw [Array.getElem_push_lt (by rw [buildAllRows_size]; omega)]
      exact ih l hlm (by omega)
    · obtain rfl : l = m := by omega
      simp [Array.getElem_push, buildAllRows_size]

/-- The precomputed table gives correct answers. -/
theorem PrecomputedRMQ.correct (a : Array ℕ) (l r : ℕ) (h : l ≤ r) (hr : r < a.size) :
    ⟪PrecomputedRMQ.query ⟪PrecomputedRMQ.make a⟫ l r⟫ = rmqNaive a l r := by
  simp only [PrecomputedRMQ.query, PrecomputedRMQ.make, ret_pure, ret_bind]
  rw [getElem!_pos _ l (by rw [buildAllRows_size]; omega),
      buildAllRows_getElem a a.size l (by omega) le_rfl,
      getElem!_pos _ (r - l) (by rw [buildRow_size]; omega),
      buildRow_getElem a l (a.size - 1 - l) (r - l) (by omega),
      rmqNaive_eq_rangeMin']
  exact rowMinVal_eq_rangeMin a l (r - l) (by omega)

/-
# RMQSolution instance
-/

instance : RMQSolution PrecomputedRMQ where
  make := PrecomputedRMQ.make
  query := PrecomputedRMQ.query
  correct := PrecomputedRMQ.correct
  make_time n := n * n
  make_time_bound := PrecomputedRMQ.make_time
  query_time _ := 0
  query_time_bound := by intro a l r; simp [PrecomputedRMQ.query_time]

end Cslib.Algorithms.Lean.TimeM
