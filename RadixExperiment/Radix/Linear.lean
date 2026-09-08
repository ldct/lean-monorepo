/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Radix.Eval.Stmt
import Std.Data.HashSet

/-! # Linear Ownership Typing for Memory Safety

A linear ownership type system that tracks which variables hold live heap
addresses. `LinearOk O s O'` says statement `s` transforms owned-set `O`
to `O'`. Programs typed `∅ → ∅` are balanced (every alloc matched by free).

The soundness theorem proves that the ownership invariant is preserved:
owned variables always point to live, distinct heap addresses.
-/

namespace Radix
open Std

abbrev Owned := HashSet String

/-- Linear ownership typing judgment. `LinearOk O s O'` means statement `s`
transforms owned-set `O` to `O'`. -/
inductive LinearOk : Owned → Stmt → Owned → Prop where
  | skip : LinearOk O .skip O
  | assign (h : x ∉ O) : LinearOk O (.assign x e) O
  | decl (h : x ∉ O) : LinearOk O (.decl x ty e) O
  | seq (h1 : LinearOk O s1 O') (h2 : LinearOk O' s2 O'') :
      LinearOk O (s1 ;; s2) O''
  | ite (ht : LinearOk O t O') (hf : LinearOk O f O') :
      LinearOk O (.ite c t f) O'
  | whileLoop (hb : LinearOk O b O) :
      LinearOk O (.while c b) O
  | alloc (h : x ∉ O) :
      LinearOk O (.alloc x ty sz) (O.insert x)
  | free (h : x ∈ O) :
      LinearOk O (.free (.var x)) (O.erase x)
  | arrSet (h : x ∈ O) :
      LinearOk O (.arrSet (.var x) idx val) O
  | ret : LinearOk O (.ret e) O
  | block (h : LinearOk O (stmts.foldl (· ;; ·) .skip) O') :
      LinearOk O (.block stmts) O'
  | callStmt : LinearOk O (.callStmt name args) O
  | scope (h : LinearOk ∅ body ∅) :
      LinearOk O (.scope params args body) O

/-- The ownership invariant: owned variables hold live, distinct heap addresses,
and the heap is well-formed (all stored addresses < nextAddr). -/
def OwnershipInv (σ : PState) (O : Owned) : Prop :=
  (∀ a, σ.heap.store.contains a → a < σ.heap.nextAddr) ∧
  (∀ x, x ∈ O →
    ∃ a, σ.getVar x = some (.addr a) ∧ σ.heap.lookup a ≠ none) ∧
  (∀ x y, x ∈ O → y ∈ O → x ≠ y →
    ∀ a b, σ.getVar x = some (.addr a) → σ.getVar y = some (.addr b) → a ≠ b)

/-- All functions in the function table have linearly balanced bodies. -/
def WellTypedFuns (funs : HashMap String FunDecl) : Prop :=
  ∀ name fd, funs.get? name = some fd → LinearOk ∅ fd.body ∅

/-! ## Auxiliary lemmas: PState -/

private theorem setVar_unfold {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') :
    ∃ fr rest, σ.frames = fr :: rest ∧
    σ' = { σ with frames := { fr with env := fr.env.set x v } :: rest } := by
  unfold PState.setVar PState.updateCurrentFrame at h
  match hf : σ.frames with
  | [] => simp [hf] at h
  | fr :: rest => simp [hf] at h; exact ⟨fr, rest, rfl, h.symm⟩

theorem PState.setVar_heap {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') : σ'.heap = σ.heap := by
  obtain ⟨fr, rest, _, rfl⟩ := setVar_unfold h; rfl

theorem PState.setVar_getVar_eq {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') : σ'.getVar x = some v := by
  obtain ⟨fr, rest, _, rfl⟩ := setVar_unfold h
  simp [PState.getVar, PState.currentFrame, Env.get?, Env.set,
        HashMap.get?_eq_getElem?]

theorem PState.setVar_getVar_ne {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') {y : String} (hne : x ≠ y) :
    σ'.getVar y = σ.getVar y := by
  obtain ⟨fr, rest, hfr, rfl⟩ := setVar_unfold h
  simp only [PState.getVar, PState.currentFrame, hfr]
  simp [Env.get?, Env.set, HashMap.get?_eq_getElem?, HashMap.getElem?_insert]
  exact fun heq => absurd heq hne

theorem PState.getVar_of_same_frames {σ₁ σ₂ : PState}
    (h : σ₁.frames = σ₂.frames) (x : String) :
    σ₁.getVar x = σ₂.getVar x := by
  simp [PState.getVar, PState.currentFrame, h]

theorem PState.setVar_frames_tail {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') : σ'.frames.tail = σ.frames.tail := by
  obtain ⟨fr, rest, hfr, rfl⟩ := setVar_unfold h; simp [hfr]

theorem PState.popFrame_heap {σ : PState} {fr : Frame} {σ' : PState}
    (h : σ.popFrame = some (fr, σ')) : σ'.heap = σ.heap := by
  unfold PState.popFrame at h
  split at h
  · contradiction
  · obtain ⟨_, rfl⟩ := h; rfl

theorem PState.popFrame_frames {σ : PState} {fr : Frame} {σ' : PState}
    (h : σ.popFrame = some (fr, σ')) : σ'.frames = σ.frames.tail := by
  unfold PState.popFrame at h
  split at h
  · contradiction
  · rename_i heq; obtain ⟨_, rfl⟩ := h; simp [heq]

theorem PState.setVar_funs {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') : σ'.funs = σ.funs := by
  obtain ⟨fr, rest, _, rfl⟩ := setVar_unfold h; rfl

theorem PState.popFrame_funs {σ : PState} {fr : Frame} {σ' : PState}
    (h : σ.popFrame = some (fr, σ')) : σ'.funs = σ.funs := by
  unfold PState.popFrame at h
  split at h
  · contradiction
  · obtain ⟨_, rfl⟩ := h; rfl

private theorem setVar_getVar_ne_of_mk {σ : PState} {heap' : Heap} {x : String} {v : Value} {σ' : PState}
    (h : (PState.mk σ.frames heap' σ.funs).setVar x v = some σ')
    {y : String} (hne : x ≠ y) :
    σ'.getVar y = σ.getVar y := by
  rw [PState.setVar_getVar_ne h hne]
  simp [PState.getVar, PState.currentFrame]

/-! ## Auxiliary lemmas: Heap -/

private theorem alloc_unfold {h : Heap} {vals : Array Value} {a : Addr} {h' : Heap}
    (ha : h.alloc vals = (a, h')) :
    a = h.nextAddr ∧ h' = { store := h.store.insert h.nextAddr vals, nextAddr := h.nextAddr + 1 } := by
  unfold Heap.alloc at ha; simp [Prod.mk.injEq] at ha; exact ⟨ha.1.symm, ha.2.symm⟩

theorem Heap.alloc_lookup_self {h : Heap} {vals : Array Value} {a : Addr} {h' : Heap}
    (ha : h.alloc vals = (a, h')) : h'.lookup a = some vals := by
  obtain ⟨rfl, rfl⟩ := alloc_unfold ha
  simp [Heap.lookup, HashMap.get?_eq_getElem?]

theorem Heap.alloc_preserves {h : Heap} {vals : Array Value} {a : Addr} {h' : Heap}
    (ha : h.alloc vals = (a, h')) {b : Addr}
    (hlive : h.lookup b ≠ none) : h'.lookup b ≠ none := by
  obtain ⟨rfl, rfl⟩ := alloc_unfold ha
  intro h_eq; apply hlive
  unfold Heap.lookup at h_eq ⊢
  simp only [HashMap.get?_eq_getElem?, HashMap.getElem?_insert] at h_eq
  split at h_eq
  · simp at h_eq
  · exact h_eq

theorem Heap.alloc_wf {h : Heap} {vals : Array Value} {a : Addr} {h' : Heap}
    (ha : h.alloc vals = (a, h'))
    (hwf : ∀ k, h.store.contains k → k < h.nextAddr) :
    ∀ k, h'.store.contains k → k < h'.nextAddr := by
  obtain ⟨rfl, rfl⟩ := alloc_unfold ha
  intro k; simp [HashMap.contains_insert]
  intro hk; rcases hk with heq | hk
  · omega
  · have := hwf k hk; omega

theorem Heap.alloc_fresh {h : Heap} {vals : Array Value} {a : Addr} {h' : Heap}
    (ha : h.alloc vals = (a, h'))
    (hwf : ∀ k, h.store.contains k → k < h.nextAddr)
    {b : Addr} (hlive : h.lookup b ≠ none) : a ≠ b := by
  obtain ⟨rfl, _⟩ := alloc_unfold ha
  intro heq; subst heq
  have hc : h.store.contains h.nextAddr := by
    unfold Heap.lookup at hlive
    simp only [HashMap.get?_eq_getElem?] at hlive
    rw [HashMap.contains_eq_isSome_getElem?]
    match hq : h.store[h.nextAddr]? with
    | none => exact absurd hq hlive
    | some _ => rfl
  exact Nat.lt_irrefl _ (hwf _ hc)

private theorem free_unfold {h : Heap} {a : Addr} {h' : Heap}
    (hf : h.free a = some h') :
    h.store.contains a ∧ h' = { h with store := h.store.erase a } := by
  unfold Heap.free at hf
  split at hf
  · simp at hf; exact ⟨‹_›, hf.symm⟩
  · simp at hf

theorem Heap.free_preserves_ne {h : Heap} {a : Addr} {h' : Heap}
    (hf : h.free a = some h') {b : Addr}
    (hne : a ≠ b) (hlive : h.lookup b ≠ none) : h'.lookup b ≠ none := by
  obtain ⟨_, rfl⟩ := free_unfold hf
  intro h_eq; apply hlive
  unfold Heap.lookup at h_eq ⊢
  simp only [HashMap.get?_eq_getElem?, HashMap.getElem?_erase] at h_eq
  split at h_eq
  · rename_i h_beq; exact absurd (beq_iff_eq.mp h_beq) hne
  · exact h_eq

theorem Heap.free_wf {h : Heap} {a : Addr} {h' : Heap}
    (hf : h.free a = some h')
    (hwf : ∀ k, h.store.contains k → k < h.nextAddr) :
    ∀ k, h'.store.contains k → k < h'.nextAddr := by
  obtain ⟨_, rfl⟩ := free_unfold hf
  intro k hk
  simp [HashMap.contains_erase] at hk
  exact hwf k hk.2

theorem Heap.write_preserves {h : Heap} {a : Addr} {i : Nat} {v : Value} {h' : Heap}
    (hw : h.write a i v = some h') {b : Addr}
    (hlive : h.lookup b ≠ none) : h'.lookup b ≠ none := by
  intro h_eq; apply hlive
  unfold Heap.write Heap.lookup at hw
  simp only [HashMap.get?_eq_getElem?] at hw
  unfold Heap.lookup at h_eq ⊢
  simp only [HashMap.get?_eq_getElem?] at h_eq ⊢
  cases ha : h.store[a]? with
  | none => simp [ha, bind, Option.bind] at hw
  | some arr =>
    simp only [ha, bind, Option.bind] at hw
    split at hw
    · simp only [Option.some.injEq] at hw
      rw [← hw, HashMap.getElem?_insert] at h_eq
      split at h_eq
      · simp at h_eq
      · exact h_eq
    · simp at hw

theorem Heap.write_wf {h : Heap} {a : Addr} {i : Nat} {v : Value} {h' : Heap}
    (hw : h.write a i v = some h')
    (hwf : ∀ k, h.store.contains k → k < h.nextAddr) :
    ∀ k, h'.store.contains k → k < h'.nextAddr := by
  intro k hk
  unfold Heap.write Heap.lookup at hw
  simp only [HashMap.get?_eq_getElem?] at hw
  cases ha : h.store[a]? with
  | none => simp [ha, bind, Option.bind] at hw
  | some arr =>
    simp only [ha, bind, Option.bind] at hw
    split at hw
    · simp only [Option.some.injEq] at hw
      subst hw; dsimp at hk ⊢
      simp [HashMap.contains_insert] at hk
      rcases hk with heq | hk
      · subst heq
        have : h.store.contains a := by
          rw [HashMap.contains_eq_isSome_getElem?]; simp [ha]
        exact hwf a this
      · exact hwf k hk
    · simp at hw

/-! ## Soundness -/

/-- Frame stack tail is preserved through BigStep execution. -/
theorem BigStep.frames_tail
    {σ : PState} {s : Stmt} {r : StmtResult}
    (h : BigStep σ s r) :
    r.state.frames.tail = σ.frames.tail := by
  induction h with
  | skip | whileFalse _ | ret _ => rfl
  | assign _ hs | decl _ hs => exact PState.setVar_frames_tail hs
  | alloc _ _ hs => have := PState.setVar_frames_tail hs; exact this
  | free _ _ | arrSet _ _ _ _ => rfl
  | seqNormal _ _ ih1 ih2 =>
    simp only [StmtResult.state] at ih1; rw [ih2, ih1]
  | seqReturn _ ih => exact ih
  | ifTrue _ _ ih | ifFalse _ _ ih => exact ih
  | whileTrue _ _ _ ih_b ih_w =>
    simp only [StmtResult.state] at ih_b; rw [ih_w, ih_b]
  | whileReturn _ _ ih => exact ih
  | block _ ih => exact ih
  | callStmt _ _ _ _ _ hpop ih =>
    simp only [StmtResult.state]
    have h1 := PState.popFrame_frames hpop
    simp only [h1, ih, PState.pushFrame, List.tail_cons]
  | scope _ _ _ _ hpop ih =>
    simp only [StmtResult.state]
    have h1 := PState.popFrame_frames hpop
    simp only [h1, ih, PState.pushFrame, List.tail_cons]

/-- After scope execution (pushFrame → body → popFrame), getVar is preserved. -/
theorem PState.getVar_scope {σ σ' : PState} {frame : Frame} {body : Stmt}
    {bodyResult : StmtResult} {fr : Frame}
    (hbody : BigStep (σ.pushFrame frame) body bodyResult)
    (hpop : bodyResult.state.popFrame = some (fr, σ')) (x : String) :
    σ'.getVar x = σ.getVar x := by
  apply PState.getVar_of_same_frames
  have h1 := PState.popFrame_frames hpop
  have h2 := BigStep.frames_tail hbody
  simp only [h1, h2, PState.pushFrame, List.tail_cons]

/-- The function table is never modified during execution. -/
theorem BigStep.funs_preserved
    {σ : PState} {s : Stmt} {r : StmtResult}
    (h : BigStep σ s r) : r.state.funs = σ.funs := by
  induction h with
  | skip | whileFalse _ | ret _ | free _ _ | arrSet _ _ _ _ => rfl
  | assign _ hs | decl _ hs => exact PState.setVar_funs hs
  | alloc _ _ hs => have h := PState.setVar_funs hs; exact h
  | seqNormal _ _ ih₁ ih₂ =>
    simp only [StmtResult.state] at ih₁; rw [ih₂, ih₁]
  | seqReturn _ ih => exact ih
  | ifTrue _ _ ih | ifFalse _ _ ih => exact ih
  | whileTrue _ _ _ ihb ihw =>
    simp only [StmtResult.state] at ihb; rw [ihw, ihb]
  | whileReturn _ _ ih => exact ih
  | block _ ih => exact ih
  | callStmt _ _ _ _ _ hpop ih =>
    simp only [StmtResult.state]; rw [PState.popFrame_funs hpop, ih]; rfl
  | scope _ _ _ _ hpop ih =>
    simp only [StmtResult.state]; rw [PState.popFrame_funs hpop, ih]; rfl

private theorem WellTypedFuns.of_normal {σ σ' : PState} {s : Stmt}
    (h : BigStep σ s (.normal σ')) (hwt : WellTypedFuns σ.funs) :
    WellTypedFuns σ'.funs := by
  have := BigStep.funs_preserved h; simp only [StmtResult.state] at this
  rw [this]; exact hwt

/-- Combined soundness + heap preservation, by induction on BigStep.
Part A: OwnershipInv preserved for normal results.
Part B: Heap wf preserved for all results.
Part C: Non-owned live addresses preserved + ownership propagation. -/
private theorem soundness_core
    {σ : PState} {s : Stmt} {r : StmtResult}
    (hstep : BigStep σ s r)
    {O O' : Owned} (hlin : LinearOk O s O')
    (hinv : OwnershipInv σ O)
    (hwt : WellTypedFuns σ.funs) :
    (∀ σ', r = .normal σ' → OwnershipInv σ' O') ∧
    (∀ k, r.state.heap.store.contains k → k < r.state.heap.nextAddr) ∧
    (∀ (a : Addr),
      σ.heap.lookup a ≠ none →
      (∀ x, x ∈ O → ∀ b, σ.getVar x = some (.addr b) → a ≠ b) →
      r.state.heap.lookup a ≠ none ∧
      (∀ σ', r = .normal σ' →
        ∀ x, x ∈ O' → ∀ b, σ'.getVar x = some (.addr b) → a ≠ b)) := by
  induction hstep generalizing O O' with
  -- Heap-unchanged cases: skip, assign, decl, ret
  | skip =>
    cases hlin
    exact ⟨fun _ h => by cases h; exact hinv, hinv.1,
           fun a hl hno => ⟨hl, fun _ h => by cases h; exact hno⟩⟩
  | assign he hs =>
    cases hlin with
    | assign hx =>
      obtain ⟨hwf, hlive, halias⟩ := hinv
      constructor
      · intro σ₁ h; cases h
        refine ⟨?_, ?_, ?_⟩
        · intro k hk; rw [PState.setVar_heap hs] at hk ⊢; exact hwf k hk
        · intro y hy
          obtain ⟨a, hget, hlook⟩ := hlive y hy
          exact ⟨a, PState.setVar_getVar_ne hs (fun h => hx (h ▸ hy)) ▸ hget,
                 PState.setVar_heap hs ▸ hlook⟩
        · intro y z hy hz hyz a b hga hgb
          rw [PState.setVar_getVar_ne hs (fun h => hx (h ▸ hy))] at hga
          rw [PState.setVar_getVar_ne hs (fun h => hx (h ▸ hz))] at hgb
          exact halias y z hy hz hyz a b hga hgb
      constructor
      · intro k hk; simp only [StmtResult.state] at hk ⊢
        rw [PState.setVar_heap hs] at hk ⊢; exact hwf k hk
      · intro a hl hno; constructor
        · simp only [StmtResult.state]; rw [PState.setVar_heap hs]; exact hl
        · intro σ₁ h; cases h; intro y hy b hgb
          rw [PState.setVar_getVar_ne hs (fun h => hx (h ▸ hy))] at hgb
          exact hno y hy b hgb
  | decl he hs =>
    cases hlin with
    | decl hx =>
      obtain ⟨hwf, hlive, halias⟩ := hinv
      constructor
      · intro σ₁ h; cases h
        refine ⟨?_, ?_, ?_⟩
        · intro k hk; rw [PState.setVar_heap hs] at hk ⊢; exact hwf k hk
        · intro y hy
          obtain ⟨a, hget, hlook⟩ := hlive y hy
          exact ⟨a, PState.setVar_getVar_ne hs (fun h => hx (h ▸ hy)) ▸ hget,
                 PState.setVar_heap hs ▸ hlook⟩
        · intro y z hy hz hyz a b hga hgb
          rw [PState.setVar_getVar_ne hs (fun h => hx (h ▸ hy))] at hga
          rw [PState.setVar_getVar_ne hs (fun h => hx (h ▸ hz))] at hgb
          exact halias y z hy hz hyz a b hga hgb
      constructor
      · intro k hk; simp only [StmtResult.state] at hk ⊢
        rw [PState.setVar_heap hs] at hk ⊢; exact hwf k hk
      · intro a hl hno; constructor
        · simp only [StmtResult.state]; rw [PState.setVar_heap hs]; exact hl
        · intro σ₁ h; cases h; intro y hy b hgb
          rw [PState.setVar_getVar_ne hs (fun h => hx (h ▸ hy))] at hgb
          exact hno y hy b hgb
  | ret he =>
    cases hlin
    exact ⟨(fun _ h => nomatch h), hinv.1,
           fun a hl hno => ⟨hl, fun _ h => nomatch h⟩⟩
  -- Composition cases
  | seqNormal h1 h2 ih1 ih2 =>
    cases hlin with
    | seq hlin1 hlin2 =>
      obtain ⟨hA1, hB1, hC1⟩ := ih1 hlin1 hinv hwt
      have hinv2 := hA1 _ rfl
      obtain ⟨hA2, hB2, hC2⟩ := ih2 hlin2 hinv2 (WellTypedFuns.of_normal h1 hwt)
      refine ⟨hA2, hB2, fun a hl hno => ?_⟩
      obtain ⟨hl2, hno2⟩ := hC1 a hl hno
      exact hC2 a hl2 (hno2 _ rfl)
  | seqReturn h1 ih1 =>
    cases hlin with
    | seq hlin1 _ =>
      obtain ⟨_, hB1, hC1⟩ := ih1 hlin1 hinv hwt
      exact ⟨(fun _ h => nomatch h), hB1,
             fun a hl hno => ⟨(hC1 a hl hno).1, fun _ h => nomatch h⟩⟩
  | ifTrue _ _ iht =>
    cases hlin with | ite hlin_t _ => exact iht hlin_t hinv hwt
  | ifFalse _ _ ihf =>
    cases hlin with | ite _ hlin_f => exact ihf hlin_f hinv hwt
  -- While cases
  | whileFalse _ =>
    cases hlin
    exact ⟨fun _ h => by cases h; exact hinv, hinv.1,
           fun a hl hno => ⟨hl, fun _ h => by cases h; exact hno⟩⟩
  | whileTrue _ hbody hwhile ih_b ih_w =>
    cases hlin with
    | whileLoop hlin_b =>
      obtain ⟨hA_b, hB_b, hC_b⟩ := ih_b hlin_b hinv hwt
      obtain ⟨hA_w, hB_w, hC_w⟩ := ih_w (.whileLoop hlin_b) (hA_b _ rfl) (WellTypedFuns.of_normal hbody hwt)
      exact ⟨hA_w, hB_w, fun a hl hno =>
        hC_w a (hC_b a hl hno).1 ((hC_b a hl hno).2 _ rfl)⟩
  | whileReturn _ _ ih_b =>
    cases hlin with
    | whileLoop hlin_b =>
      obtain ⟨_, hB_b, hC_b⟩ := ih_b hlin_b hinv hwt
      exact ⟨(fun _ h => nomatch h), hB_b,
             fun a hl hno => ⟨(hC_b a hl hno).1, fun _ h => nomatch h⟩⟩
  -- Alloc
  | alloc hsz ha hs =>
    cases hlin with
    | @alloc O xv _ _ hx =>
      obtain ⟨hwf, hlive, halias⟩ := hinv
      constructor
      · -- Part A
        intro σ₁ h; cases h
        refine ⟨?_, ?_, ?_⟩
        · intro k hk
          have hh := PState.setVar_heap hs; rw [hh] at hk ⊢
          exact Heap.alloc_wf ha hwf k hk
        · intro y hy
          simp [HashSet.mem_insert] at hy
          rcases hy with heq | hy
          · subst heq
            refine ⟨_, PState.setVar_getVar_eq hs, ?_⟩
            have hh := PState.setVar_heap hs; rw [hh]
            intro h; simp [Heap.alloc_lookup_self ha] at h
          · obtain ⟨b, hget, hlook⟩ := hlive y hy
            refine ⟨b, ?_, ?_⟩
            · exact (setVar_getVar_ne_of_mk hs (fun h => hx (h ▸ hy))) ▸ hget
            · have hh := PState.setVar_heap hs; rw [hh]
              exact Heap.alloc_preserves ha hlook
        · intro y z hy hz hyz a' b' hga hgb
          simp [HashSet.mem_insert] at hy hz
          rcases hy with heqy | hy <;> rcases hz with heqz | hz
          · exact absurd (heqy.symm.trans heqz) hyz
          · subst heqy
            rw [PState.setVar_getVar_eq hs] at hga; simp at hga; subst hga
            rw [setVar_getVar_ne_of_mk hs (fun h => hx (h ▸ hz))] at hgb
            obtain ⟨_, hgetc, hlookc⟩ := hlive z hz
            rw [hgetc] at hgb; simp at hgb; subst hgb
            exact Heap.alloc_fresh ha hwf hlookc
          · subst heqz
            rw [PState.setVar_getVar_eq hs] at hgb; simp at hgb; subst hgb
            rw [setVar_getVar_ne_of_mk hs (fun h => hx (h ▸ hy))] at hga
            obtain ⟨_, hgetc, hlookc⟩ := hlive y hy
            rw [hgetc] at hga; simp at hga; subst hga
            exact (Heap.alloc_fresh ha hwf hlookc).symm
          · rw [setVar_getVar_ne_of_mk hs (fun h => hx (h ▸ hy))] at hga
            rw [setVar_getVar_ne_of_mk hs (fun h => hx (h ▸ hz))] at hgb
            exact halias y z hy hz hyz a' b' hga hgb
      constructor
      · -- Part B
        intro k hk; simp only [StmtResult.state] at hk ⊢
        rw [PState.setVar_heap hs] at hk ⊢; exact Heap.alloc_wf ha hwf k hk
      · -- Part C
        intro a hl hno; constructor
        · simp only [StmtResult.state]
          rw [PState.setVar_heap hs]; exact Heap.alloc_preserves ha hl
        · intro σ₁ h; cases h; intro y hy b hgb
          simp [HashSet.mem_insert] at hy
          rcases hy with heq | hy
          · subst heq
            rw [PState.setVar_getVar_eq hs] at hgb; simp at hgb; subst hgb
            exact (Heap.alloc_fresh ha hwf hl).symm
          · rw [setVar_getVar_ne_of_mk hs (fun h => hx (h ▸ hy))] at hgb
            exact hno y hy b hgb
  -- Free
  | free he hf =>
    cases hlin with
    | @free O x hx =>
      simp only [Expr.eval] at he
      obtain ⟨hwf, hlive, halias⟩ := hinv
      constructor
      · -- Part A
        intro σ₁ h; cases h
        refine ⟨Heap.free_wf hf hwf, ?_, ?_⟩
        · intro y hy
          simp [HashSet.mem_erase] at hy
          obtain ⟨hne, hy⟩ := hy
          obtain ⟨b, hget, hlook⟩ := hlive y hy
          exact ⟨b, hget, Heap.free_preserves_ne hf (halias x y hx hy hne _ _ he hget) hlook⟩
        · intro y z hy hz hyz a' b' hga hgb
          simp [HashSet.mem_erase] at hy hz
          exact halias y z hy.2 hz.2 hyz a' b' hga hgb
      constructor
      · -- Part B
        intro k hk; exact Heap.free_wf hf hwf k hk
      · -- Part C
        intro addr hl hno
        constructor
        · exact Heap.free_preserves_ne hf (fun h => by subst h; exact hno x hx _ he rfl) hl
        · intro σ₁ h; cases h; intro y hy b hgb
          simp [HashSet.mem_erase] at hy
          exact hno y hy.2 b hgb
  -- ArrSet
  | arrSet harr hidx hval hw =>
    cases hlin with
    | arrSet hx =>
      obtain ⟨hwf, hlive, halias⟩ := hinv
      constructor
      · intro σ₁ h; cases h
        exact ⟨Heap.write_wf hw hwf,
          fun y hy => by
            obtain ⟨b, hget, hlook⟩ := hlive y hy
            exact ⟨b, hget, Heap.write_preserves hw hlook⟩,
          halias⟩
      constructor
      · intro k hk; exact Heap.write_wf hw hwf k hk
      · intro a hl hno
        exact ⟨Heap.write_preserves hw hl, fun σ₁ h => by cases h; exact hno⟩
  -- Block
  | block _ ih =>
    cases hlin with | block h => exact ih h hinv hwt
  -- CallStmt — uses WellTypedFuns to get the body's linear typing
  | callStmt hlook _ _ _ hbody hpop ih =>
    cases hlin
    have hlin_body := hwt _ _ hlook
    obtain ⟨hA, hB, hC⟩ := ih hlin_body
      ⟨hinv.1, fun _ h => absurd h HashSet.not_mem_empty,
                fun _ _ h => absurd h HashSet.not_mem_empty⟩ hwt
    have hhp := PState.popFrame_heap hpop
    have hgv := PState.getVar_scope hbody hpop
    obtain ⟨hwf, hlive, halias⟩ := hinv
    simp only [StmtResult.state]
    constructor
    · -- Part A
      intro σ₁ h; cases h
      refine ⟨?_, ?_, ?_⟩
      · intro k hk; rw [hhp] at hk ⊢; exact hB k hk
      · intro y hy
        obtain ⟨b, hget, hlook'⟩ := hlive y hy
        refine ⟨b, ?_, ?_⟩
        · rw [hgv y]; exact hget
        · rw [hhp]; exact (hC b hlook' (fun _ h => absurd h HashSet.not_mem_empty)).1
      · intro y z hy hz hyz a' b' hga hgb
        rw [hgv y] at hga; rw [hgv z] at hgb
        exact halias y z hy hz hyz a' b' hga hgb
    constructor
    · -- Part B
      intro k hk; rw [hhp] at hk ⊢; exact hB k hk
    · -- Part C
      intro a hl hno
      constructor
      · rw [hhp]; exact (hC a hl (fun _ h => absurd h HashSet.not_mem_empty)).1
      · intro σ₁ h; cases h; intro y hy b hgb
        apply hno y hy b; rw [← hgv y]; exact hgb
  -- Scope — the key case requiring heap preservation
  | scope hargs hlen hframe hbody hpop ih =>
    cases hlin with
    | scope hlin_body =>
      obtain ⟨hA, hB, hC⟩ := ih hlin_body
        ⟨hinv.1, fun _ h => absurd h HashSet.not_mem_empty,
                  fun _ _ h => absurd h HashSet.not_mem_empty⟩ hwt
      have hhp := PState.popFrame_heap hpop
      have hgv := PState.getVar_scope hbody hpop
      obtain ⟨hwf, hlive, halias⟩ := hinv
      simp only [StmtResult.state]
      constructor
      · -- Part A
        intro σ₁ h; cases h
        refine ⟨?_, ?_, ?_⟩
        · intro k hk; rw [hhp] at hk ⊢; exact hB k hk
        · intro y hy
          obtain ⟨b, hget, hlook⟩ := hlive y hy
          refine ⟨b, ?_, ?_⟩
          · rw [hgv y]; exact hget
          · rw [hhp]; exact (hC b hlook (fun _ h => absurd h HashSet.not_mem_empty)).1
        · intro y z hy hz hyz a' b' hga hgb
          rw [hgv y] at hga; rw [hgv z] at hgb
          exact halias y z hy hz hyz a' b' hga hgb
      constructor
      · -- Part B
        intro k hk; rw [hhp] at hk ⊢; exact hB k hk
      · -- Part C
        intro a hl hno
        constructor
        · rw [hhp]; exact (hC a hl (fun _ h => absurd h HashSet.not_mem_empty)).1
        · intro σ₁ h; cases h; intro y hy b hgb
          apply hno y hy b; rw [← hgv y]; exact hgb

theorem LinearOk.soundness
    {O O' : Owned} {s : Stmt}
    (hlin : LinearOk O s O')
    {σ σ' : PState}
    (hstep : BigStep σ s (.normal σ'))
    (hinv : OwnershipInv σ O)
    (hwt : WellTypedFuns σ.funs) :
    OwnershipInv σ' O' :=
  (soundness_core hstep hlin hinv hwt).1 σ' rfl

/-- After executing a linearly-typed statement, every owned variable
points to a live heap address. -/
theorem LinearOk.live_access
    {O O' : Owned} {s : Stmt}
    (hlin : LinearOk O s O')
    {σ σ' : PState}
    (hstep : BigStep σ s (.normal σ'))
    (hinv : OwnershipInv σ O)
    (hwt : WellTypedFuns σ.funs)
    {x : String} (hx : x ∈ O') :
    ∃ a, σ'.getVar x = some (.addr a) ∧ σ'.heap.lookup a ≠ none :=
  (LinearOk.soundness hlin hstep hinv hwt).2.1 x hx

/-- Programs typed ∅ → ∅ are balanced: starting from a valid state with no
ownership, execution preserves the heap well-formedness invariant. -/
theorem LinearOk.balanced
    {s : Stmt}
    (hlin : LinearOk ∅ s ∅)
    {σ σ' : PState}
    (hstep : BigStep σ s (.normal σ'))
    (hwf : ∀ a, σ.heap.store.contains a → a < σ.heap.nextAddr)
    (hwt : WellTypedFuns σ.funs) :
    ∀ a, σ'.heap.store.contains a → a < σ'.heap.nextAddr := by
  have hinv : OwnershipInv σ ∅ :=
    ⟨hwf, fun _ h => absurd h (HashSet.not_mem_empty),
          fun _ _ h => absurd h (HashSet.not_mem_empty)⟩
  exact (LinearOk.soundness hlin hstep hinv hwt).1

end Radix
