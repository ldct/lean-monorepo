import Radix.Proofs.Hoare

/-! Shared validation facts. These apply to executable guards and bounded array
writes, rather than assuming that an external input decoder is correct. -/
namespace Radix.ABC177C

/-- Every initialized array cell is an unsigned input within the benchmark bound. -/
def BoundedValues (values : Array Value) : Prop :=
  ∀ i (hi : i < values.size), ∃ n : UInt64, values[i]'hi = .uint64 n ∧ n.toNat ≤ 1000000000

theorem bounded_zeros (n : Nat) :
    BoundedValues (Array.replicate n (.uint64 0)) := by
  intro i hi
  exact ⟨0, by simp, by decide⟩

theorem bounded_set {values : Array Value} (h : BoundedValues values)
    (i : Nat) (hi : i < values.size) (n : UInt64) (hn : n.toNat ≤ 1000000000) :
    BoundedValues (values.set i (.uint64 n)) := by
  intro j hj
  by_cases he : i = j
  · subst j; exact ⟨n, by simp, hn⟩
  · obtain ⟨v, hv, hb⟩ := h j (by simpa using hj)
    exact ⟨v, by simpa [Array.getElem_set, he] using hv, hb⟩

/-- A successful intentional exclusion guard establishes the negated condition. -/
theorem validation_false
    (h : BigStep σ (.ite condition (.block [.reject]) .skip) (.normal σ')) :
    condition.eval σ = some (.bool false) ∧ σ' = σ := by
  cases h with
  | ifTrue hc hb =>
    cases hb with
    | block hb =>
      cases hb with
      | seqNormal hs hr => cases hr
  | ifFalse hc hs => cases hs; exact ⟨hc, rfl⟩

/-- Input validation can preserve a bound over every cell, including cells that
are still zero, without exposing any token-decoding premise in refinement. -/
theorem bounded_heap_write {heap heap' : Heap} {a : Addr} {i : Nat} {n : UInt64}
    (hw : heap.write a i (.uint64 n) = some heap')
    (hn : n.toNat ≤ 1000000000)
    (hvalues : ∀ values, heap.lookup a = some values → BoundedValues values) :
    ∃ values, heap'.lookup a = some values ∧ BoundedValues values := by
  unfold Heap.write at hw
  cases hl : heap.lookup a with
  | none => simp [hl] at hw
  | some values =>
    simp only [hl, bind, Option.bind] at hw
    split at hw
    · rename_i hi
      simp only [Option.some.injEq] at hw
      subst heap'
      exact ⟨_, by simp [Heap.lookup], bounded_set (hvalues values hl) i hi n hn⟩
    · simp at hw

end Radix.ABC177C
