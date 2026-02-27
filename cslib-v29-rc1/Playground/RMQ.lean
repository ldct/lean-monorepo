import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Log
import Mathlib.Order.WithBot
import Plausible

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

-- minimum of xs[l..r] inclusive
def rmqNaive (xs : Array ℕ) (l r : ℕ) : WithTop ℕ :=
  (xs.drop l |>.take (r - l + 1)).toList.minimum

/-
# Sparse Table

Define a structure SparseTable which preprocesses an array of integers for fast RMQ queries.
- make : Array ℕ → SparseTable
- query : SparseTable → ℕ → ℕ → ℕ
-/

structure SparseTable where
  table : Array (Array ℕ)

/-- Map `f` over `[0, ..., n-1]`, sequencing the `TimeM` effects. -/
private def tickMap (f : ℕ → TimeM ℕ) : ℕ → TimeM (Array ℕ)
  | 0 => return #[]
  | n + 1 => do
    let arr ← tickMap f n
    let v ← f n
    return arr.push v

@[simp] private lemma tickMap_size (f : ℕ → TimeM ℕ) : ∀ n, ⟪tickMap f n⟫.size = n
  | 0 => by simp [tickMap]
  | n + 1 => by simp [tickMap, tickMap_size f n]

private lemma tickMap_time_eq (f : ℕ → TimeM ℕ) (c : ℕ) (hf : ∀ i, (f i).time = c) :
    ∀ n, (tickMap f n).time = n * c
  | 0 => by simp [tickMap]
  | n + 1 => by simp [tickMap, tickMap_time_eq f c hf n, hf n, Nat.add_mul]

private lemma tickMap_getElem (f : ℕ → TimeM ℕ) : ∀ (n : ℕ) (i : ℕ) (hi : i < n),
    (⟪tickMap f n⟫[i]'(by simp; omega)) = ⟪f i⟫
  | 0, _, hi => by omega
  | n + 1, i, hi => by
    grind [tickMap, tickMap_size, tickMap_getElem f n]

/-- Compute the first `m` levels of the sparse table, where the ith level stores all minimums of contiguous subarrays of length 2^i. The tick cost is how many `min` calls are made. -/
private def buildTable (a : Array ℕ) : ℕ → TimeM (Array (Array ℕ))
  | 0 => do return #[a]
  | m + 1 => do
    let st ← buildTable a m
    let newRow ← tickMap (fun j => do ✓ return min st[m]![j]! st[m]![j + 2 ^ m]!) (a.size - 2 ^ (m + 1) + 1)
    return st.push newRow

@[grind =] private lemma buildTable_size (a : Array ℕ) : ∀ m, ⟪buildTable a m⟫.size = m + 1
  | 0 => by simp [buildTable]
  | m + 1 => by simp [buildTable, buildTable_size a m]

def SparseTable.make (a : Array ℕ) : TimeM SparseTable := do
  if a.size == 0 then
    return { table := #[] }
  else
    let t ← buildTable a (Nat.log 2 a.size)
    return { table := t }

#eval (SparseTable.make #[3, 1, 4, 1, 5, 9, 2, 6]).time

def SparseTable.query (st : SparseTable) (l r : ℕ) : TimeM ℕ := do
  let len := r - l + 1
  let k := Nat.log 2 len
  ✓ return min st.table[k]![l]! st.table[k]![r + 1 - 2 ^ k]!

/-
# Quickcheck of SparseTable.make

Check that SparseTable.make generates the correct table as the python code (verification by eval'ing examples).
Expected values obtained via: echo "3 1 4 1 5 9 2 6" | python3 sparsetable.py
-/

/--info: true-/ #guard_msgs in
#eval ⟪SparseTable.make #[3, 1, 4, 1, 5, 9, 2, 6]⟫.table == #[#[3, 1, 4, 1, 5, 9, 2, 6], #[1, 1, 1, 1, 5, 2, 2], #[1, 1, 1, 1, 2], #[1]]

/--info: true-/ #guard_msgs in
#eval ⟪SparseTable.make #[5]⟫.table == #[#[5]]

/--info: true-/ #guard_msgs in
#eval ⟪SparseTable.make #[10, 20]⟫.table == #[#[10, 20], #[10]]

/--info: true-/ #guard_msgs in
#eval ⟪SparseTable.make #[7, 2, 9, 4, 3, 1, 8]⟫.table == #[#[7, 2, 9, 4, 3, 1, 8], #[2, 2, 4, 3, 1, 1], #[2, 2, 1, 1]]

/-
# Verification of SparseTable.query

Formally prove that SparseTable solves the RMQ problem.
-/

/-- The length-len minimum starting at `start` -/
def rangeMin (xs : List ℕ) (start len : ℕ) : WithTop ℕ :=
  (xs.drop start |>.take len).minimum

/-- Splitting a contiguous range into two parts -/
lemma rangeMin_split (xs : List ℕ) (j a b : ℕ) :
    rangeMin xs j (a + b) = min (rangeMin xs j a) (rangeMin xs (j + a) b) := by
  grind [List.minimum_append, List.drop_drop, rangeMin]

/-- Two overlapping ranges of length 2^k cover a range of length len -/
lemma rangeMin_overlap (xs : List ℕ) (l len k : ℕ)
    (hk : 2 ^ k ≤ len) (hlen : len < 2 ^ (k + 1)) :
    min (rangeMin xs l (2 ^ k)) (rangeMin xs (l + len - 2 ^ k) (2 ^ k))
    = rangeMin xs l len := by
  set s := len - 2 ^ k
  have : s + 2 ^ k = len := by omega
  have : rangeMin xs l (2 ^ k) = min (rangeMin xs l s) (rangeMin xs (l + s) (2 ^ k - s)) := by
    rw [show 2 ^ k = s + (2 ^ k - s) by omega]; grind [rangeMin_split]
  have : rangeMin xs (l + s) (2 ^ k) =
      min (rangeMin xs (l + s) (2 ^ k - s)) (rangeMin xs (l + 2 ^ k) s) := by
    rw [show 2 ^ k = (2 ^ k - s) + s by omega]; rw [rangeMin_split]; grind
  grind [rangeMin_split]

@[grind =] private lemma rangeMin_one (xs : List ℕ) (j : ℕ) (hj : j < _) :
    rangeMin xs j 1 = xs[j] := by
  grind [List.drop_eq_getElem_cons, List.take_add_one, List.minimum_singleton, rangeMin]

@[grind =] private lemma buildTable_eq_make (a : Array ℕ) (ha : 0 < a.size) :
    ⟪SparseTable.make a⟫.table = ⟪buildTable a (Nat.log 2 a.size)⟫ := by
  simp [SparseTable.make, Nat.ne_of_gt ha]

@[grind =] private lemma buildTable_row_size (a : Array ℕ) (m : ℕ) (hm : 2 ^ m ≤ a.size)
    (i : ℕ) (hi : i ≤ m) :
    (⟪buildTable a m⟫[i]'(by grind)).size = a.size - 2 ^ i + 1 := by
  induction m with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp [buildTable]; omega
  | succ m ih =>
    by_cases him : i ≤ m
    · have hlt : i < ⟪buildTable a m⟫.size := by grind
      simp only [buildTable, ret_bind, ret_pure]; rw [Array.getElem_push_lt hlt]
      exact ih (le_trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ m)) hm) him
    · obtain rfl : i = m + 1 := by omega
      grind [buildTable, tickMap_size]

private theorem buildTable_invariant (a : Array ℕ) (m : ℕ)
    (hm : 2 ^ m ≤ a.size) (i j : ℕ) (hi : i ≤ m) (hj : j + 2 ^ i ≤ a.size) :
    ((⟪buildTable a m⟫[i]'(by rw [buildTable_size]; omega))[j]'(by
      rw [buildTable_row_size a m hm i hi]; omega)) =
      rangeMin a.toList j (2 ^ i) := by
  induction m generalizing i j with
  | zero =>
    obtain rfl : i = 0 := by omega
    grind [buildTable]
  | succ m ih =>
    have : 2 ^ m ≤ a.size := le_trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ m)) hm
    by_cases him : i ≤ m
    · grind [buildTable, Array.getElem_push_lt]
    · obtain rfl : i = m + 1 := by omega
      conv_rhs => rw [show 2 ^ (m + 1) = 2 ^ m + 2 ^ m by grind]
      rw [rangeMin_split]
      simp [buildTable, Array.getElem_push, buildTable_size]
      grind [tickMap_getElem, tickMap_size, WithTop.coe_min]

/-- Each table entry stores the range minimum for a power-of-2 length -/
theorem table_invariant (a : Array ℕ) (ha : 0 < a.size) (i j : ℕ)
    (hi : i < _) (hj : j < _) :
    ((⟪SparseTable.make a⟫.table[i])[j]) = rangeMin a.toList j (2 ^ i) := by
  have hm : 2 ^ Nat.log 2 a.size ≤ a.size := by grind [Nat.pow_log_le_self]
  have : 2 ^ i ≤ a.size := by
    grw [← hm]; apply Nat.pow_le_pow_right <;> grind
  grind [buildTable_row_size, buildTable_size, buildTable_invariant]

private lemma rmqNaive_eq_rangeMin (vals : Array ℕ) (l r : ℕ) :
    rmqNaive vals l r = rangeMin vals.toList l (r - l + 1) := by
  grind [rmqNaive, rangeMin, Array.toList_extract]

theorem correct (vals : Array ℕ) (l r : ℕ) (h : l ≤ r) (hr : r < vals.size)
: ⟪⟪SparseTable.make vals⟫.query l r⟫ = rmqNaive vals l r := by
  rw [rmqNaive_eq_rangeMin]
  have ha : 0 < vals.size := by omega
  set len := r - l + 1; set k := Nat.log 2 len
  have hpow_le : 2 ^ k ≤ len := by grind [Nat.pow_log_le_self]
  have hpow_lt : len < 2 ^ (k + 1) := by grind [Nat.lt_pow_succ_log_self]
  have hk_le : k ≤ Nat.log 2 vals.size := Nat.log_mono_right (by omega)
  have hk_lt : k < ⟪SparseTable.make vals⟫.table.size := by
    rw [buildTable_eq_make vals ha, buildTable_size]; omega
  have : (⟪SparseTable.make vals⟫.table[k]'hk_lt).size = vals.size - 2 ^ k + 1 := by
    simp only [buildTable_eq_make vals ha]
    exact buildTable_row_size vals _ (by grind [Nat.pow_log_le_self]) k hk_le
  rw [← rangeMin_overlap vals.toList l len k hpow_le hpow_lt]
  grind [SparseTable.query, WithTop.coe_min, table_invariant]

/-
# Quickcheck of SparseTable.query
-/

def randArray (size : ℕ) : IO (Array ℕ) := do
  let mut arr : Array ℕ := #[]
  for _ in [:size] do
    let v ← IO.rand 0 200
    arr := arr.push v
  return arr

def SparseTable.verifyOne (vals : Array ℕ) : Bool :=
  let st := ⟪SparseTable.make vals⟫
  Id.run do
    let mut ok := true
    for l in [:vals.size] do
      for r in [l:vals.size] do
        if rmqNaive vals l r != ↑(⟪st.query l r⟫) then
          ok := false
    return ok

def SparseTable.verify : IO Bool := do
  IO.setRandSeed 42
  let mut ok := true
  for sz in [1:51] do
    let arr ← randArray sz
    if !SparseTable.verifyOne arr then
      ok := false
  return ok

/--info: true-/ #guard_msgs in #eval SparseTable.verify

/-
# Time complexity of SparseTable.make

The cost model counts array element operations (min comparisons) for building the table.
At each level k (1 ≤ k ≤ ⌊log₂ n⌋), we build a row of size n - 2^k + 1 ≤ n.
Total cost is therefore at most n * ⌊log₂ n⌋.
-/

private lemma buildTable_time (a : Array ℕ) (ha : 0 < a.size) :
    ∀ m, (buildTable a m).time ≤ a.size * m
  | 0 => by simp [buildTable]
  | m + 1 => by
    let f : ℕ → TimeM ℕ := fun j => do
      ✓ return min (⟪buildTable a m⟫)[m]![j]! (⟪buildTable a m⟫)[m]![j + 2 ^ m]!
    have hft : (tickMap f (a.size - 2 ^ (m + 1) + 1)).time = a.size - 2 ^ (m + 1) + 1 := by
      rw [tickMap_time_eq f 1 (by intro; simp [f])]; simp
    simp only [buildTable, time_bind, time_pure]
    have ih := buildTable_time a ha m
    grind

/-- The construction time of a sparse table is at most n * ⌊log₂ n⌋. -/
theorem SparseTable.make_time (a : Array ℕ) :
    (SparseTable.make a).time ≤ a.size * Nat.log 2 a.size := by
  by_cases ha : 0 < a.size
  · simp [SparseTable.make, Nat.ne_of_gt ha]
    exact buildTable_time a ha (Nat.log 2 a.size)
  · have h0 : a.size = 0 := by omega
    simp [SparseTable.make, h0]

/-
# Time complexity of SparseTable.query
-/

/-- A single query costs O(1). -/
theorem SparseTable.query_time (st : SparseTable) (l r : ℕ) :
    (st.query l r).time = 1 := by
  simp [SparseTable.query]

/-
A type class for stating that `α` is a solution to the RMQ problem.

- `make` : preprocess an array of values `a`, returning an `α`
- `query` : query `α` for the minimum value in a subarray of `a`
- `correct` : the result is the same as the naive implementation
- `make_time`, `query_time` : the time complexity of `make` and `query`, as a function of `|a|`
- `make_time_bound`, `query_time_bound` : proofs of the time complexity bounds
-/
structure RMQSolution (α : Type) where
  make : Array ℕ → TimeM α
  query : α → ℕ → ℕ → TimeM ℕ
  correct (a : Array ℕ) (l r : ℕ) (h : l ≤ r) (hr : r < a.size) :
    (⟪query ⟪make a⟫ l r⟫) = rmqNaive a l r
  make_time : ℕ → ℕ
  make_time_bound : ∀ a : Array ℕ, (make a).time ≤ make_time a.size
  query_time : ℕ → ℕ
  query_time_bound : ∀ a : Array ℕ, ∀ l r : ℕ, (query ⟪make a⟫ l r).time ≤ query_time a.size

instance : RMQSolution SparseTable where
  make := SparseTable.make
  query := SparseTable.query
  correct := correct
  make_time n := n * Nat.log 2 n
  make_time_bound := SparseTable.make_time
  query_time _ := 1
  query_time_bound := by simp [SparseTable.query_time]

/-
# Wall-clock benchmark of SparseTable
-/

def SparseTable.benchmark (n : ℕ := 100) (numQueries : ℕ := n) : IO Unit := do
  IO.setRandSeed 12345

  -- Build random array
  let mut arr : Array ℕ := Array.mkEmpty n
  for _ in [:n] do
    arr := arr.push (← IO.rand 0 1000000)

  -- Build sparse table (print table size to force evaluation)
  let t0 ← IO.monoMsNow
  let st := ⟪SparseTable.make arr⟫
  IO.println s!"Table levels: {st.table.size}"
  let t1 ← IO.monoMsNow
  IO.println s!"Build time: {t1 - t0} ms  (n = {n})"

  -- Generate random queries
  let mut queries : Array (ℕ × ℕ) := Array.mkEmpty numQueries
  for _ in [:numQueries] do
    let a ← IO.rand 0 (n - 1)
    let b ← IO.rand 0 (n - 1)
    queries := queries.push (min a b, max a b)

  -- Run queries
  let t2 ← IO.monoMsNow
  let mut checksum := 0
  for (l, r) in queries do
    checksum := checksum + ⟪st.query l r⟫
  let t3 ← IO.monoMsNow
  IO.println s!"Query time: {t3 - t2} ms  ({numQueries} queries)"
  IO.println s!"Checksum: {checksum}"

#eval SparseTable.benchmark

end Cslib.Algorithms.Lean.TimeM
