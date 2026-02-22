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

/-- Recursive version of table construction -/
private def buildTable (a : Array ℕ) : ℕ → Array (Array ℕ)
  | 0 => #[a]
  | m + 1 =>
    let st := buildTable a m
    st.push ((Array.range (a.size - 2 ^ (m + 1) + 1)).map fun j =>
      min st[m]![j]! st[m]![j + 2 ^ m]!)

@[grind =] private lemma buildTable_size (a : Array ℕ) : ∀ m, (buildTable a m).size = m + 1
  | 0 => by simp [buildTable]
  | m + 1 => by simp [buildTable, buildTable_size a m]

def SparseTable.make (a : Array ℕ) : SparseTable := {
  table :=
    if a.size == 0 then #[]
    else buildTable a (Nat.log 2 a.size)
}

def SparseTable.query (st : SparseTable) (l r : ℕ) : ℕ :=
  let len := r - l + 1
  let k := Nat.log 2 len
  min st.table[k]![l]! st.table[k]![r + 1 - 2 ^ k]!

/-
# Quickcheck of SparseTable.make

Check that SparseTable.make generates the correct table as the python code (verification by eval'ing examples).
Expected values obtained via: echo "3 1 4 1 5 9 2 6" | python3 sparsetable.py
-/

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[3, 1, 4, 1, 5, 9, 2, 6]).table == #[#[3, 1, 4, 1, 5, 9, 2, 6], #[1, 1, 1, 1, 5, 2, 2], #[1, 1, 1, 1, 2], #[1]]

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[5]).table == #[#[5]]

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[10, 20]).table == #[#[10, 20], #[10]]

/--info: true-/ #guard_msgs in
#eval (SparseTable.make #[7, 2, 9, 4, 3, 1, 8]).table == #[#[7, 2, 9, 4, 3, 1, 8], #[2, 2, 4, 3, 1, 1], #[2, 2, 1, 1]]

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
  set s := len - 2 ^ k with hs_def
  have hlen_eq : s + 2 ^ k = len := by omega
  -- Decompose the left range: 2^k = s + (2^k - s)
  have hleft : rangeMin xs l (2 ^ k) = min (rangeMin xs l s) (rangeMin xs (l + s) (2 ^ k - s)) := by
    rw [show 2 ^ k = s + (2 ^ k - s) by omega]
    grind [rangeMin_split]
  -- Decompose the right range: 2^k = (2^k - s) + s
  have hright : rangeMin xs (l + s) (2 ^ k) =
      min (rangeMin xs (l + s) (2 ^ k - s)) (rangeMin xs (l + 2 ^ k) s) := by
    rw [show 2 ^ k = (2 ^ k - s) + s by omega]
    rw [rangeMin_split]
    grind
  grind [rangeMin_split]

@[grind =] private lemma rangeMin_one (xs : List ℕ) (j : ℕ) (hj : j < _) :
    rangeMin xs j 1 = xs[j] := by
  grind [List.drop_eq_getElem_cons, List.take_add_one, List.minimum_singleton, rangeMin]

@[grind =] private lemma buildTable_eq_make (a : Array ℕ) (ha : 0 < a.size) :
    (SparseTable.make a).table = buildTable a (Nat.log 2 a.size) := by
  simp only [SparseTable.make, beq_iff_eq]; split <;> grind

@[grind =] private lemma buildTable_row_size (a : Array ℕ) (m : ℕ) (hm : 2 ^ m ≤ a.size)
    (i : ℕ) (hi : i ≤ m) :
    ((buildTable a m)[i]'(by grind)).size = a.size - 2 ^ i + 1 := by
  induction m with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    simp [buildTable]; omega
  | succ m ih =>
    by_cases him : i ≤ m
    · have hlt : i < (buildTable a m).size := by grind
      simp only [buildTable]
      rw [Array.getElem_push_lt hlt]
      exact ih (le_trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ m)) hm) him
    · have him_eq : i = m + 1 := by omega
      subst him_eq
      grind [buildTable, Array.size_range]

private theorem buildTable_invariant (a : Array ℕ) (m : ℕ)
    (hm : 2 ^ m ≤ a.size) (i j : ℕ) (hi : i ≤ m) (hj : j + 2 ^ i ≤ a.size) :
    (((buildTable a m)[i]'(by rw [buildTable_size]; omega))[j]'(by
      rw [buildTable_row_size a m hm i hi]; omega)) =
      rangeMin a.toList j (2 ^ i) := by
  induction m generalizing i j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    grind [buildTable]
  | succ m ih =>
    have hm' : 2 ^ m ≤ a.size :=
      le_trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ m)) hm
    by_cases him : i ≤ m
    · grind [buildTable, Array.getElem_push_lt]
    · -- New row (i = m + 1)
      have him_eq : i = m + 1 := by omega
      subst him_eq
      -- Prepare bounds
      have pow_eq : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by grind
      conv_rhs => rw [pow_eq]
      rw [rangeMin_split]
      simp [buildTable, Array.getElem_push, buildTable_size,
            Array.getElem_map, Array.getElem_range]
      grind

/-- Each table entry stores the range minimum for a power-of-2 length -/
theorem table_invariant (a : Array ℕ) (ha : 0 < a.size) (i j : ℕ)
    (hi : i < _)
    (hj : j < _)
: (((SparseTable.make a).table[i])[j]) = rangeMin a.toList j (2 ^ i) := by
  have hm : 2 ^ Nat.log 2 a.size ≤ a.size := by grind [Nat.pow_log_le_self]
  have : 2 ^ i ≤ a.size := by
    grw [← hm]
    apply Nat.pow_le_pow_right <;> grind [buildTable_size]
  grind [buildTable_row_size, buildTable_size, buildTable_invariant]

private lemma rmqNaive_eq_rangeMin (vals : Array ℕ) (l r : ℕ) :
    rmqNaive vals l r = rangeMin vals.toList l (r - l + 1) := by
  grind [rmqNaive, rangeMin, Array.toList_extract]

theorem correct (vals : Array ℕ) (l r : ℕ) (h : l ≤ r) (hr : r < vals.size)
: (SparseTable.make vals).query l r = rmqNaive vals l r := by
  rw [rmqNaive_eq_rangeMin]
  have ha : 0 < vals.size := by omega
  set len := r - l + 1 with hlen_def
  set k := Nat.log 2 len with hk_def
  have hlen_pos : 0 < len := by omega
  have hlen_le : len ≤ vals.size := by omega
  have hpow_le : 2 ^ k ≤ len := by grind [Nat.pow_log_le_self]
  have hpow_lt : len < 2 ^ (k + 1) := by grind [Nat.lt_pow_succ_log_self]
  have hk_le : k ≤ Nat.log 2 vals.size := Nat.log_mono_right hlen_le
  have htable_sz : (SparseTable.make vals).table.size = Nat.log 2 vals.size + 1 := by
    rw [buildTable_eq_make vals ha, buildTable_size]
  have hk_lt : k < (SparseTable.make vals).table.size := by omega
  have hrow_sz : ((SparseTable.make vals).table[k]'hk_lt).size = vals.size - 2 ^ k + 1 := by
    simp only [buildTable_eq_make vals ha]
    exact buildTable_row_size vals _ (by grind [Nat.pow_log_le_self]) k hk_le
  have hl_lt : l < ((SparseTable.make vals).table[k]'hk_lt).size := by rw [hrow_sz]; omega
  have hr1_lt : r + 1 - 2 ^ k < ((SparseTable.make vals).table[k]'hk_lt).size := by
    grind
  have inv1 :=table_invariant vals ha k l hk_lt hl_lt
  have inv2 := table_invariant vals ha k (r + 1 - 2 ^ k) hk_lt hr1_lt
  rw [← rangeMin_overlap vals.toList l len k hpow_le hpow_lt]
  grind [SparseTable.query, WithTop.coe_min]

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
  let st := SparseTable.make vals
  Id.run do
    let mut ok := true
    for l in [:vals.size] do
      for r in [l:vals.size] do
        if rmqNaive vals l r != ↑(st.query l r) then
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

end Cslib.Algorithms.Lean.TimeM
