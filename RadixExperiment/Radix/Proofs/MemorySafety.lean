import Radix.Eval.Stmt

/-! Allocations persist, including their lengths, across execution.
The bump allocator's well-formedness condition excludes fabricated initial heaps
whose next address is already allocated. Standard initial heaps satisfy it. -/
namespace Radix
open Std

def Heap.WellFormed (h : Heap) : Prop :=
  ∀ a, h.lookup a ≠ none → a < h.nextAddr

def Heap.Extends (h h' : Heap) : Prop :=
  ∀ a n, h.arraySize a = some n → h'.arraySize a = some n

theorem Heap.Extends.refl (h : Heap) : h.Extends h := fun _ _ h => h

theorem Heap.Extends.trans {h₁ h₂ h₃ : Heap}
    (h12 : h₁.Extends h₂) (h23 : h₂.Extends h₃) : h₁.Extends h₃ :=
  fun a n h => h23 a n (h12 a n h)

theorem Heap.empty_wellFormed : Heap.WellFormed {} := by
  simp [WellFormed, lookup]

theorem Heap.alloc_persistent {h : Heap} (vals : Array Value)
    (wf : h.WellFormed) :
    (h.alloc vals).2.WellFormed ∧ h.Extends (h.alloc vals).2 := by
  constructor
  · intro a ha
    simp only [alloc, lookup, HashMap.get?_eq_getElem?, HashMap.getElem?_insert] at ha
    split at ha
    · rename_i heq; simp only [beq_iff_eq] at heq
      change a < h.nextAddr + 1
      rw [← heq]
      exact Nat.lt_succ_self _
    · have hold : h.lookup a ≠ none := ha
      have hh : a < h.nextAddr := wf a hold
      change a < h.nextAddr + 1
      exact Nat.lt_succ_of_lt hh
  · intro a n hn
    have live : h.lookup a ≠ none := by
      intro he; simp [arraySize, he] at hn
    have hne : h.nextAddr ≠ a := (Nat.ne_of_lt (wf a live)).symm
    simpa [alloc, arraySize, lookup, HashMap.get?_eq_getElem?,
      HashMap.getElem?_insert, hne] using hn

theorem Heap.write_persistent {h h' : Heap} {a : Addr} {i : Nat} {v : Value}
    (hw : h.write a i v = some h') (wf : h.WellFormed) :
    h'.WellFormed ∧ h.Extends h' := by
  unfold write at hw
  cases hl : h.lookup a with
  | none => simp [hl] at hw
  | some arr =>
    simp only [hl, bind, Option.bind] at hw
    split at hw
    · simp only [Option.some.injEq] at hw
      subst h'
      constructor
      · intro b hb
        by_cases he : a = b
        · subst b; exact wf a (by simp [hl])
        · apply wf b
          simpa [lookup, HashMap.get?_eq_getElem?, HashMap.getElem?_insert, he] using hb
      · intro b n hn
        by_cases he : a = b
        · subst b
          have hn' : arr.size = n := by simpa [arraySize, hl] using hn
          simpa [arraySize, lookup, HashMap.get?_eq_getElem?] using hn'
        · simpa [arraySize, lookup, HashMap.get?_eq_getElem?, HashMap.getElem?_insert, he] using hn
    · simp at hw

theorem Heap.read_within_bounds (h : Heap) (a : Addr) (i : Nat) {arr : Array Value}
    (hlookup : h.lookup a = some arr) (hbounds : i < arr.size) :
    ∃ v, h.read a i = some v := by
  simp [Heap.read, hlookup, Array.getElem?_eq_getElem hbounds]

private theorem setVar_heap {σ σ' : PState} {x : String} {v : Value}
    (hs : σ.setVar x v = some σ') : σ'.heap = σ.heap := by
  unfold PState.setVar PState.updateCurrentFrame at hs
  split at hs
  · contradiction
  · cases hs; rfl

private theorem popFrame_heap {σ σ' : PState} {fr : Frame}
    (hs : σ.popFrame = some (fr, σ')) : σ'.heap = σ.heap := by
  unfold PState.popFrame at hs
  split at hs
  · contradiction
  · cases hs; rfl

private theorem afterCall_heap (r : StmtResult) (σ : PState) :
    (r.afterCall σ).state.heap = σ.heap := by
  cases r <;> rfl

theorem BigStep.heap_persistent (h : BigStep σ s r) (wf : σ.heap.WellFormed) :
    r.state.heap.WellFormed ∧ σ.heap.Extends r.state.heap := by
  induction h with
  | skip | ret | reject | whileFalse | writeU64 | writeText | expectEof | eofReject | readReject =>
    exact ⟨wf, .refl _⟩
  | assign he hs | decl he hs | readU64 he hs =>
    simp only [StmtResult.state, setVar_heap hs]
    exact ⟨wf, .refl _⟩
  | seqNormal h₁ h₂ ih₁ ih₂ | whileTrue hc hb hw ih₁ ih₂ =>
    have ha := ih₁ wf
    have hb := ih₂ ha.1
    exact ⟨hb.1, ha.2.trans hb.2⟩
  | seqReturn h ih | seqReject h ih | ifTrue hc h ih | ifFalse hc h ih
  | whileReturn hc h ih | whileReject hc h ih | block h ih => exact ih wf
  | alloc hsz ha hs =>
    rename_i a heap' σ₀ σ₁ x ty szExpr sz
    have hp := Heap.alloc_persistent (Array.replicate sz.toNat (.uint64 0)) wf
    rw [ha] at hp
    simpa only [StmtResult.state, setVar_heap hs] using hp
  | arrSet harr hidx hval hw => exact Heap.write_persistent hw wf
  | callStmt hlook hargs hparams hframe hbody hpop ih
  | scope hargs hparams hframe hbody hpop ih =>
    have hp := ih wf
    simpa only [afterCall_heap, popFrame_heap hpop, PState.pushFrame] using hp

/-- Every array present initially is still present with exactly its initial length. -/
theorem BigStep.allocation_lengths_preserved (h : BigStep σ s r)
    (wf : σ.heap.WellFormed) (ha : σ.heap.arraySize a = some n) :
    r.state.heap.arraySize a = some n :=
  (h.heap_persistent wf).2 a n ha

end Radix
