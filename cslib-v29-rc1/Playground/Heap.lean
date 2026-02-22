import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Log

set_option autoImplicit false
namespace Cslib.Algorithms.Lean.TimeM
open List

/-! # Binary Min-Heap on List ℕ

We implement a binary min-heap on `List ℕ` with:
- `heapPush` — insert an element
- `heapPop` — extract the minimum

Main results:
- `root_eq_minimum` — the root of a min-heap is its minimum element
- `heapPush_perm` — `heapPush` preserves elements (modulo permutation)
-/

/-! ## Definitions -/

/-- The min-heap property: every node is ≤ its children.
Uses implicit tree indexing where parent of `i` is `(i-1)/2`. -/
def IsMinHeap (h : List ℕ) : Prop :=
  ∀ (i : ℕ), 0 < i → (hi : i < h.length) → h[(i - 1) / 2] ≤ h[i]

/-- Swap elements at positions `i` and `j` in a list. -/
def listSwap (l : List ℕ) (i j : ℕ) : List ℕ :=
  if hi : i < l.length then
    if hj : j < l.length then
      (l.set i l[j]).set j l[i]
    else l
  else l

@[simp]
theorem listSwap_length (l : List ℕ) (i j : ℕ) : (listSwap l i j).length = l.length := by
  unfold listSwap
  split
  · split <;> simp
  · rfl

/-- Index of the smallest child of node `i`, or `none` if `i` is a leaf. -/
def minChild (h : List ℕ) (i : ℕ) : Option ℕ :=
  let left := 2 * i + 1
  let right := 2 * i + 2
  if hl : left < h.length then
    if hr : right < h.length then
      if h[left] ≤ h[right] then some left else some right
    else some left
  else none

lemma minChild_gt (h : List ℕ) (i j : ℕ) (hmc : minChild h i = some j) : i < j := by
  simp only [minChild] at hmc
  split at hmc
  · split at hmc
    · split at hmc <;> (simp at hmc; omega)
    · simp at hmc; omega
  · simp at hmc

lemma minChild_bound (h : List ℕ) (i j : ℕ) (hmc : minChild h i = some j) : j < h.length := by
  simp only [minChild] at hmc
  split at hmc
  · split at hmc
    · split at hmc <;> (simp at hmc; omega)
    · simp at hmc; omega
  · simp at hmc

/-- Fix a heap violation at index `i` by repeatedly swapping with parent. -/
def siftUp (h : List ℕ) (i : ℕ) : List ℕ :=
  if i = 0 then h
  else if hp : (i - 1) / 2 < h.length then
    if hi : i < h.length then
      if h[i] < h[(i - 1) / 2] then
        siftUp (listSwap h i ((i - 1) / 2)) ((i - 1) / 2)
      else h
    else h
  else h
termination_by i

/-- Fix a heap violation at index `i` by repeatedly swapping with smallest child. -/
def siftDown (h : List ℕ) (i : ℕ) : List ℕ :=
  match hmc : minChild h i with
  | none => h
  | some j =>
    if hj : j < h.length then
      if hi : i < h.length then
        if h[j] < h[i] then
          siftDown (listSwap h i j) j
        else h
      else h
    else h
termination_by h.length - i
decreasing_by
  simp only [listSwap_length]
  have := minChild_gt h i j hmc
  omega

/-- Insert element `x` into the heap. -/
def heapPush (h : List ℕ) (x : ℕ) : List ℕ :=
  let h' := h ++ [x]
  siftUp h' (h'.length - 1)

/-- Extract the minimum element from a non-empty heap.
Returns the minimum and the remaining heap. -/
def heapPop (h : List ℕ) (hne : h ≠ []) : ℕ × List ℕ :=
  let root := h.head hne
  if h.length ≤ 1 then (root, [])
  else
    let h' := listSwap h 0 (h.length - 1)
    let h'' := h'.dropLast
    (root, siftDown h'' 0)

-- Sanity checks
#eval heapPush (heapPush (heapPush [] 3) 1) 2
#eval heapPop [1, 3, 2] (by simp)

/-! ## Tier 0: listSwap lemmas -/

theorem listSwap_getElem (l : List ℕ) (i j k : ℕ) (hi : i < l.length) (hj : j < l.length)
    (hk : k < l.length) :
    (listSwap l i j)[k]'(by simp; exact hk) =
    if k = j then l[i] else if k = i then l[j] else l[k] := by
  simp only [listSwap, hi, hj, dite_true]
  -- Goal: ((l.set i l[j]).set j l[i])[k] = if k = j then l[i] else if k = i then l[j] else l[k]
  by_cases hjk : k = j
  · subst hjk; simp
  · by_cases hik : k = i
    · subst hik
      rw [List.getElem_set_of_ne (Ne.symm hjk)]
      simp [hjk]
    · rw [List.getElem_set_of_ne (Ne.symm hjk), List.getElem_set_of_ne (Ne.symm hik)]
      simp [hjk, hik]

private lemma swap_head_perm (a : ℕ) (l : List ℕ) (j : ℕ) (hj : j < l.length) :
    l[j] :: l.set j a ~ a :: l :=
  calc l[j] :: l.set j a
      ~ l[j] :: (a :: l.eraseIdx j) := Perm.cons _ (set_perm_cons_eraseIdx hj a)
    _ ~ a :: (l[j] :: l.eraseIdx j) := Perm.swap _ _ _
    _ ~ a :: l := Perm.cons _ (getElem_cons_eraseIdx_perm hj)

theorem listSwap_perm (l : List ℕ) (i j : ℕ) (hi : i < l.length) (hj : j < l.length) :
    listSwap l i j ~ l := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    unfold listSwap; simp only [hi, hj, dite_true]
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.set_cons_zero, List.getElem_cons_succ,
                    List.set_cons_succ, List.getElem_cons_zero]
        exact swap_head_perm a l j (by simpa using hj)
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.set_cons_succ,
                    List.getElem_cons_succ, List.set_cons_zero]
        exact swap_head_perm a l i (by simpa using hi)
      | succ j =>
        simp only [List.set_cons_succ, List.getElem_cons_succ]
        have hi' : i < l.length := by simpa using hi
        have hj' : j < l.length := by simpa using hj
        have h := ih i j hi' hj'
        simp only [listSwap, hi', hj', dite_true] at h
        exact Perm.cons a h

/-! ## Tier 1: IsMinHeap basics -/

theorem isMinHeap_nil : IsMinHeap [] := by
  intro i hi him; simp at him

theorem isMinHeap_singleton (x : ℕ) : IsMinHeap [x] := by
  intro i hi him; simp at him; omega

theorem isMinHeap_root_le (h : List ℕ) (hm : IsMinHeap h)
    (i : ℕ) (hi : i < h.length) :
    h[0]'(by omega) ≤ h[i] := by
  if h0 : i = 0 then
    subst h0; exact le_refl _
  else
    have hpi : (i - 1) / 2 < h.length := by omega
    exact Nat.le_trans (isMinHeap_root_le h hm ((i - 1) / 2) hpi) (hm i (by omega) hi)
termination_by i

/-! ## Tier 2: root = minimum -/

theorem root_eq_minimum (h : List ℕ) (hm : IsMinHeap h) (hne : h ≠ []) :
    h.minimum = ↑(h[0]'(List.length_pos_of_ne_nil hne)) := by
  apply le_antisymm
  · -- minimum ≤ ↑h[0]: since h[0] ∈ h
    exact List.minimum_le_of_mem' (List.getElem_mem ..)
  · -- ↑h[0] ≤ minimum: since h[0] ≤ all elements
    apply List.le_minimum_of_forall_le
    intro a ha
    rw [List.mem_iff_getElem] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact WithTop.coe_le_coe.mpr (isMinHeap_root_le h hm i hi)

/-! ## Tier 3: Length and permutation invariants -/

theorem siftUp_length (h : List ℕ) (i : ℕ) : (siftUp h i).length = h.length := by
  unfold siftUp
  split
  · rfl
  · split
    · split
      · split
        · rw [siftUp_length]; simp
        · rfl
      · rfl
    · rfl
termination_by i

theorem siftUp_perm (h : List ℕ) (i : ℕ) : siftUp h i ~ h := by
  unfold siftUp
  split
  · exact List.Perm.refl _
  · split
    · split
      · split
        · rename_i hi0 hp hi _
          calc siftUp (listSwap h i ((i - 1) / 2)) ((i - 1) / 2)
              ~ listSwap h i ((i - 1) / 2) := siftUp_perm _ _
            _ ~ h := listSwap_perm h i ((i - 1) / 2) hi hp
        · exact List.Perm.refl _
      · exact List.Perm.refl _
    · exact List.Perm.refl _
termination_by i

theorem siftDown_length (h : List ℕ) (i : ℕ) : (siftDown h i).length = h.length := by
  fun_induction siftDown h i with
  | case1 => rfl
  | case2 _ _ _ _ _ _ _ ih => rw [ih, listSwap_length]
  | _ => rfl

theorem siftDown_perm (h : List ℕ) (i : ℕ) : siftDown h i ~ h := by
  fun_induction siftDown h i with
  | case1 => exact Perm.refl _
  | case2 _ _ _ _ _ _ _ ih => exact ih.trans (listSwap_perm _ _ _ ‹_› ‹_›)
  | _ => exact Perm.refl _

theorem heapPush_perm (h : List ℕ) (x : ℕ) : heapPush h x ~ h ++ [x] := by
  unfold heapPush
  exact siftUp_perm _ _

/-! ## Tier 4: Heap preservation -/

/-- Heap property holds everywhere except possibly at index `pos`
(i.e., `h[(pos-1)/2]` might be > `h[pos]`). -/
def IsMinHeapExceptAt (h : List ℕ) (pos : ℕ) : Prop :=
  ∀ (i : ℕ), 0 < i → i ≠ pos → (hi : i < h.length) → h[(i - 1) / 2] ≤ h[i]

/-- Heap property holds everywhere except that `h[pos]` might be > its children. -/
def IsMinHeapExceptDown (h : List ℕ) (pos : ℕ) : Prop :=
  ∀ (i : ℕ), 0 < i → (i - 1) / 2 ≠ pos → (hi : i < h.length) → h[(i - 1) / 2] ≤ h[i]

theorem siftUp_isMinHeap (h : List ℕ) (i : ℕ)
    (hex : IsMinHeapExceptAt h i) (hi : i < h.length) :
    IsMinHeap (siftUp h i) := by
  sorry

theorem siftDown_isMinHeap (h : List ℕ) (i : ℕ)
    (hex : IsMinHeapExceptDown h i) (hi : i < h.length) :
    IsMinHeap (siftDown h i) := by
  sorry

theorem heapPush_isMinHeap (h : List ℕ) (x : ℕ) (hm : IsMinHeap h) :
    IsMinHeap (heapPush h x) := by
  sorry

theorem heapPop_isMinHeap (h : List ℕ) (hne : h ≠ []) (hm : IsMinHeap h) :
    IsMinHeap (heapPop h hne).2 := by
  sorry

/-! ## Tier 5: Pop returns minimum -/

theorem heapPop_fst_eq_head (h : List ℕ) (hne : h ≠ []) :
    (heapPop h hne).1 = h.head hne := by
  unfold heapPop
  split <;> rfl

end Cslib.Algorithms.Lean.TimeM
