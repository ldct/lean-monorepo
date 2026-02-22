import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Log
import Mathlib.Order.WithBot
import Plausible

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

-- Naive spec: minimum of xs[l..l+len) as WithTop ℕ (⊤ for empty ranges)
def rangeMinW (xs : List ℕ) (l len : ℕ) : WithTop ℕ :=
  (xs.drop l |>.take len).minimum

-- Sparse table: sparseTableVal xs i j = min of xs[j..j+2^i)
def sparseTableVal (xs : List ℕ) : ℕ → ℕ → ℕ
  | 0, j => xs[j]!
  | i + 1, j => min (sparseTableVal xs i j) (sparseTableVal xs i (j + 2^i))

-- Query: min of xs[l..r) using overlap trick with floor-log
def rmq (xs : List ℕ) (l r : ℕ) : ℕ :=
  let len := r - l
  let k := Nat.log 2 len
  min (sparseTableVal xs k l) (sparseTableVal xs k (r - 2^k))

structure SparseTable where
  table : Array (Array ℕ)

def SparseTable.make (a : Array ℕ) : SparseTable := {
  table :=
    if a.size == 0 then #[]
    else Id.run do
      let n := a.size
      let k := Nat.log 2 n + 1
      let mut st : Array (Array ℕ) := #[a]
      for i in [1:k] do
        let half := 2 ^ (i - 1)
        let rowLen := n - 2 ^ i + 1
        let prev := st[i - 1]!
        let mut row : Array ℕ := Array.mkEmpty rowLen
        for j in [:rowLen] do
          row := row.push (min prev[j]! prev[j + half]!)
        st := st.push row
      return st
}

-- Python: echo "3 1 4 1 5 9 2 6" | python3 sparsetable.py
-- st = [[3, 1, 4, 1, 5, 9, 2, 6], [1, 1, 1, 1, 5, 2, 2], [1, 1, 1, 1, 2], [1]]
#eval (SparseTable.make #[3, 1, 4, 1, 5, 9, 2, 6]).table

-- Helper: splitting a sublist into two contiguous parts
lemma list_take_add (ys : List ℕ) (m n : ℕ) :
    ys.take (m + n) = ys.take m ++ (ys.drop m).take n := by
  induction ys generalizing m n with
  | nil => simp
  | cons y ys ih =>
    cases m with
    | zero => simp
    | succ m => simp [ih m n, Nat.succ_add]

lemma take_add_split (xs : List ℕ) (l len1 len2 : ℕ) :
    ((xs.drop l).take (len1 + len2)) =
    ((xs.drop l).take len1) ++ ((xs.drop (l + len1)).take len2) := by
  rw [list_take_add, List.drop_drop]

-- Singleton range minimum equals the element
lemma rangeMinW_singleton (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    rangeMinW xs j 1 = ↑(xs[j]) := by
  simp only [rangeMinW]
  rw [List.drop_eq_getElem_cons hj, List.take_succ_cons, List.take_zero]
  exact List.minimum_singleton _

-- Range minimum splits over contiguous subranges
lemma rangeMinW_split (xs : List ℕ) (l len1 len2 : ℕ) :
    rangeMinW xs l (len1 + len2) =
    min (rangeMinW xs l len1) (rangeMinW xs (l + len1) len2) := by
  simp only [rangeMinW, take_add_split, List.minimum_append]

-- Overlap lemma: min over two overlapping power-of-2 ranges = min over union
-- min(min(a,b), min(b,c)) = min(a, min(b,c)) in any linear order
private lemma min_overlap {α : Type*} [LinearOrder α] (a b c : α) :
    min (min a b) (min b c) = min a (min b c) := by
  apply le_antisymm
  · -- ≤: min(min(a,b), min(b,c)) ≤ min(a, min(b,c))
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · apply le_min
      · exact le_trans (min_le_left _ _) (min_le_right _ _)
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
  · -- ≥: min(a, min(b,c)) ≤ min(min(a,b), min(b,c))
    apply le_min
    · -- min(a, min(b,c)) ≤ min(a,b): need ≤ a and ≤ b
      exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · -- min(a, min(b,c)) ≤ min(b,c): since min(a,min(b,c)) ≤ min(b,c)
      exact min_le_right _ _

lemma rangeMinW_overlap (xs : List ℕ) (l len k : ℕ)
    (hk1 : 2^k ≤ len) (hk2 : len ≤ 2^(k+1)) :
    min (rangeMinW xs l (2^k)) (rangeMinW xs (l + len - 2^k) (2^k)) =
    rangeMinW xs l len := by
  -- Let p = len - 2^k, q = 2*2^k - len
  -- Decompose into 3 contiguous parts with widths p, q, p
  -- Left query covers p+q = 2^k, right covers q+p = 2^k, full covers p+q+p = len
  set p := len - 2^k
  set q := 2 * 2^k - len
  have hpq : p + q = 2^k := by omega
  have hqp : q + p = 2^k := by omega
  have hstart : l + len - 2^k = l + p := by omega
  -- Define the three base terms
  set α := rangeMinW xs l p
  set β := rangeMinW xs (l + p) q
  set γ := rangeMinW xs (l + p + q) p
  -- Decompose left query
  have h_left : rangeMinW xs l (2^k) = min α β := by
    rw [← hpq]; exact rangeMinW_split xs l p q
  -- Decompose right query
  have h_right : rangeMinW xs (l + len - 2^k) (2^k) = min β γ := by
    rw [hstart, ← hqp]; exact rangeMinW_split xs (l + p) q p
  -- Decompose full range: len = p + (q + p)
  have hlen_eq : len = p + (q + p) := by omega
  have h_full : rangeMinW xs l len = min α (min β γ) := by
    conv_lhs => rw [hlen_eq]
    rw [rangeMinW_split xs l p (q + p), rangeMinW_split xs (l + p) q p]
  -- Conclude
  rw [h_left, h_right, h_full]
  exact min_overlap (α := WithTop ℕ) _ _ _

-- Sparse table agrees with rangeMinW when in bounds
theorem sparseTableVal_correct (xs : List ℕ) (i j : ℕ) (hj : j + 2^i ≤ xs.length) :
    ↑(sparseTableVal xs i j) = rangeMinW xs j (2^i) := by
  induction i generalizing j with
  | zero =>
    simp only [sparseTableVal, Nat.pow_zero]
    rw [getElem!_pos xs j (by omega)]
    exact (rangeMinW_singleton xs j (by omega)).symm
  | succ i ih =>
    simp only [sparseTableVal]
    have hj1 : j + 2^i ≤ xs.length := by
      have : 2^i ≤ 2^(i+1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hj2 : (j + 2^i) + 2^i ≤ xs.length := by
      have : 2^i + 2^i = 2^(i+1) := by omega
      omega
    rw [WithTop.coe_min, ih j hj1, ih (j + 2^i) hj2]
    have : (2 : ℕ)^(i + 1) = 2^i + 2^i := by omega
    rw [this]
    exact (rangeMinW_split xs j (2^i) (2^i)).symm

-- Main correctness theorem
theorem rmq_correct (xs : List ℕ) (l r : ℕ) (hlr : l < r) (hr : r ≤ xs.length)
    (hlen : r - l ≥ 1) :
    ↑(rmq xs l r) = rangeMinW xs l (r - l) := by
  simp only [rmq]
  set len := r - l
  have hlen_pos : len ≥ 1 := by omega
  have hlen_ne : len ≠ 0 := by omega
  set k := Nat.log 2 len
  have hk1 : 2^k ≤ len := Nat.pow_log_le_self 2 hlen_ne
  have hk2 : len < 2^(k+1) := Nat.lt_pow_succ_log_self (by omega) len
  -- bounds for sparseTableVal_correct
  have hlen_eq : len = r - l := rfl
  have hrl : l + len = r := by omega
  have hst1 : l + 2^k ≤ xs.length := by
    calc l + 2^k ≤ l + len := by omega
    _ = r := hrl
    _ ≤ xs.length := hr
  have h2k_le_r : 2^k ≤ r := by
    calc 2^k ≤ len := hk1
    _ = r - l := rfl
    _ ≤ r := Nat.sub_le r l
  have hst2 : (r - 2^k) + 2^k ≤ xs.length := by omega
  rw [WithTop.coe_min, sparseTableVal_correct xs k l hst1,
      sparseTableVal_correct xs k (r - 2^k) hst2]
  -- now need: min (rangeMinW xs l (2^k)) (rangeMinW xs (r - 2^k) (2^k)) = rangeMinW xs l len
  have hrl : r - 2^k = l + len - 2^k := by omega
  rw [hrl]
  exact rangeMinW_overlap xs l len k hk1 (by omega)

end Cslib.Algorithms.Lean.TimeM
