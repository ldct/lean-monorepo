/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Stmt
import Std.Data.HashMap

/-! # Copy Propagation

Replace `x := y; ... x ...` with `... y ...` when safe. Uses a `CopyMap`
tracking which variables are known copies of others.

The key invariant is `CopyMap.agrees`: for every mapping `x -> y` in the
copy map, `sigma.getVar x = sigma.getVar y` in the current state. This
invariant is maintained across assignments (by invalidating stale entries)
and is reset to empty at control flow joins (if/else, while, function calls)
to stay sound.

The correctness proof (`Stmt.copyProp_correct`) is the most complex of the
optimization proofs because it must track the copy map invariant through
every statement form, including the special case of `x := y` (copy assignment)
vs. `x := e` (general assignment).
-/

namespace Radix
open Std

abbrev CopyMap := HashMap String String

/-- Apply copy propagation to an expression using the given copy map. -/
def Expr.copyProp (m : CopyMap) : Expr → Expr
  | .lit v => .lit v
  | .var x => .var (m.get? x |>.getD x)
  | .binop op l r => .binop op (l.copyProp m) (r.copyProp m)
  | .unop op e => .unop op (e.copyProp m)
  | .arrGet arr idx => .arrGet (arr.copyProp m) (idx.copyProp m)
  | .arrLen arr => .arrLen (arr.copyProp m)
  | .strLen s => .strLen (s.copyProp m)
  | .strGet s idx => .strGet (s.copyProp m) (idx.copyProp m)

def Expr.copyPropList (m : CopyMap) (es : List Expr) : List Expr :=
  es.map (Expr.copyProp m)

mutual
/-- Apply copy propagation to a statement. Returns the transformed statement
and an updated copy map. -/
def Stmt.copyProp (m : CopyMap) : Stmt → Stmt × CopyMap
  | .skip => (.skip, m)
  | .assign x (.var y) =>
    let y' := m.get? y |>.getD y
    (.assign x (.var y'), m.insert x y' |>.erase y |> fun m' =>
      m'.filter fun _ v => v != x)
  | .assign x e =>
    let e' := Expr.copyProp m e
    let m' := m.erase x |>.filter fun _ v => v != x
    (.assign x e', m')
  | .seq s₁ s₂ =>
    let (s₁', m₁) := s₁.copyProp m
    let (s₂', m₂) := s₂.copyProp m₁
    (.seq s₁' s₂', m₂)
  | .ite c t f =>
    let c' := Expr.copyProp m c
    let (t', _) := t.copyProp m
    let (f', _) := f.copyProp m
    (.ite c' t' f', {})
  | .while c b =>
    let c' := Expr.copyProp {} c
    let (b', _) := b.copyProp {}
    (.while c' b', {})
  | .decl x ty e =>
    let e' := Expr.copyProp m e
    let m' := m.erase x |>.filter fun _ v => v != x
    (.decl x ty e', m')
  | .alloc x ty sz =>
    let sz' := Expr.copyProp m sz
    let m' := m.erase x |>.filter fun _ v => v != x
    (.alloc x ty sz', m')
  | .free e => (.free (Expr.copyProp m e), m)
  | .arrSet arr idx val =>
    (.arrSet (Expr.copyProp m arr) (Expr.copyProp m idx) (Expr.copyProp m val), m)
  | .ret e => (.ret (Expr.copyProp m e), m)
  | .block stmts =>
    let (stmts', m') := Stmt.copyPropList m stmts
    (.block stmts', m')
  | .callStmt f args =>
    (.callStmt f (Expr.copyPropList m args), {})
  | .scope ps as body =>
    (.scope ps (Expr.copyPropList m as) (body.copyProp {}).1, {})

def Stmt.copyPropList (m : CopyMap) : List Stmt → List Stmt × CopyMap
  | [] => ([], m)
  | s :: ss =>
    let (s', m') := s.copyProp m
    let (ss', m'') := Stmt.copyPropList m' ss
    (s' :: ss', m'')
end

def Stmt.copyPropagation (s : Stmt) : Stmt :=
  (s.copyProp {}).1

/-! ## Map Agreement Invariant -/

/-- The copy map agrees with a state if every recorded copy `x -> y`
holds at runtime: the variables `x` and `y` have the same value. -/
def CopyMap.agrees (m : CopyMap) (σ : PState) : Prop :=
  ∀ x y, m.get? x = some y → σ.getVar x = σ.getVar y

theorem CopyMap.agrees_empty (σ : PState) : ({} : CopyMap).agrees σ :=
  fun x y h => absurd (show ({} : CopyMap)[x]? = some y from h) (by simp)

/-! ## State Interaction Lemmas -/

private theorem PState.getVar_setVar_eq {σ σ' : PState} {x : String} {v : Value}
    (hs : σ.setVar x v = some σ') :
    σ'.getVar x = some v := by
  unfold PState.setVar PState.updateCurrentFrame at hs
  match hf : σ.frames with
  | [] => simp [hf] at hs
  | fr :: rest =>
    simp [hf] at hs; obtain ⟨rfl⟩ := hs
    unfold PState.getVar PState.currentFrame
    simp only [Env.get?, Env.set, List.head?]
    show (fr.env.insert x v)[x]? = some v; simp

private theorem PState.getVar_setVar_ne {σ σ' : PState} {x y : String} {v : Value}
    (hs : σ.setVar x v = some σ') (hne : y ≠ x) :
    σ'.getVar y = σ.getVar y := by
  unfold PState.setVar PState.updateCurrentFrame at hs
  match hf : σ.frames with
  | [] => simp [hf] at hs
  | fr :: rest =>
    simp [hf] at hs; obtain ⟨rfl⟩ := hs
    unfold PState.getVar PState.currentFrame
    simp only [Env.get?, Env.set, List.head?]
    show (fr.env.insert x v)[y]? = (do let fr ← σ.frames.head?; fr.env[y]?)
    rw [hf]; simp [HashMap.getElem?_insert]
    intro heq; exact absurd heq hne.symm

/-! ## Expression Copy Propagation Correctness -/

theorem Expr.copyProp_eval (m : CopyMap) (e : Expr) (σ : PState) (hm : m.agrees σ) :
    (e.copyProp m).eval σ = e.eval σ := by
  induction e with
  | lit v => simp [Expr.copyProp, Expr.eval]
  | var x =>
    simp only [Expr.copyProp, Expr.eval, Option.getD]
    split
    · next y hy => exact (hm x y hy).symm
    · rfl
  | binop op l r ihl ihr => simp only [Expr.copyProp, Expr.eval, ihl, ihr]
  | unop op e ih => simp only [Expr.copyProp, Expr.eval, ih]
  | arrGet arr idx iha ihi => simp only [Expr.copyProp, Expr.eval, iha, ihi]
  | arrLen arr ih => simp only [Expr.copyProp, Expr.eval, ih]
  | strLen s ih => simp only [Expr.copyProp, Expr.eval, ih]
  | strGet s idx ihs ihi => simp only [Expr.copyProp, Expr.eval, ihs, ihi]

private theorem Expr.copyPropList_mapM_eval (m : CopyMap) (args : List Expr) (σ : PState)
    (hm : m.agrees σ) :
    (Expr.copyPropList m args).mapM (Expr.eval σ) = args.mapM (Expr.eval σ) := by
  unfold Expr.copyPropList
  induction args with
  | nil => simp
  | cons e es ih => simp only [List.map_cons, List.mapM_cons, Expr.copyProp_eval m e σ hm, ih]

/-! ## Helper: copy-propagated variable lookup -/

private theorem getVar_copyProp_var (m : CopyMap) (y : String) (σ : PState)
    (hm : m.agrees σ) :
    σ.getVar (m.get? y |>.getD y) = σ.getVar y := by
  simp [Option.getD]; split
  · next z hz => exact (hm y z hz).symm
  · rfl

/-! ## Map Agreement After Assignment -/

private theorem agrees_after_erase_filter
    (m : CopyMap) (x : String) (σ σ' : PState)
    (hm : m.agrees σ)
    (hne : ∀ z, z ≠ x → σ'.getVar z = σ.getVar z) :
    CopyMap.agrees (m.erase x |>.filter fun _ v => v != x) σ' := by
  intro a b h
  change (m.erase x |>.filter fun _ w => w != x)[a]? = some b at h
  simp [HashMap.getElem?_erase] at h
  obtain ⟨⟨hanx, hab⟩, hbnx⟩ := h
  have ha : a ≠ x := fun h => hanx (h ▸ rfl)
  have hb : b ≠ x := fun h => hbnx (h ▸ rfl)
  rw [hne a ha, hne b hb]; exact hm a b hab

private theorem agrees_after_assign_var
    (m : CopyMap) (x y : String) (σ σ' : PState) (v : Value)
    (hm : m.agrees σ)
    (heval : σ.getVar y = some v)
    (heqx : σ'.getVar x = some v)
    (hne : ∀ z, z ≠ x → σ'.getVar z = σ.getVar z) :
    let y' := m.get? y |>.getD y
    CopyMap.agrees (m.insert x y' |>.erase y |>.filter fun _ v => v != x) σ' := by
  intro y' a b h
  change (m.insert x y' |>.erase y |>.filter fun _ w => w != x)[a]? = some b at h
  simp [HashMap.getElem?_erase, HashMap.getElem?_insert] at h
  obtain ⟨⟨hany, hab⟩, hbnx⟩ := h
  have hb_ne_x : b ≠ x := fun h => hbnx (h ▸ rfl)
  by_cases hxa : x = a
  · subst hxa; simp at hab; subst hab
    rw [heqx, hne y' hb_ne_x]
    exact (getVar_copyProp_var m y σ hm ▸ heval).symm
  · simp [hxa] at hab
    rw [hne a (Ne.symm hxa), hne b hb_ne_x]; exact hm a b hab

/-! ## Foldl/CopyPropList Distributivity -/

private theorem copyProp_foldl_seq_fst (m : CopyMap) (acc : Stmt) (stmts : List Stmt) :
    ((stmts.foldl (init := acc) (· ;; ·)).copyProp m).1 =
    ((Stmt.copyPropList (acc.copyProp m).2 stmts).1.foldl
      (init := (acc.copyProp m).1) (· ;; ·)) := by
  induction stmts generalizing acc m with
  | nil => simp [List.foldl, Stmt.copyPropList]
  | cons s ss ih =>
    simp only [List.foldl, Stmt.copyPropList]
    rw [ih]; simp only [Stmt.copyProp]

private theorem copyProp_foldl_skip_fst (m : CopyMap) (stmts : List Stmt) :
    ((stmts.foldl (init := Stmt.skip) (· ;; ·)).copyProp m).1 =
    ((Stmt.copyPropList m stmts).1.foldl (init := Stmt.skip) (· ;; ·)) := by
  have := copyProp_foldl_seq_fst m Stmt.skip stmts
  simp [Stmt.copyProp] at this; exact this

private theorem copyProp_foldl_seq_snd (m : CopyMap) (acc : Stmt) (stmts : List Stmt) :
    ((stmts.foldl (init := acc) (· ;; ·)).copyProp m).2 =
    (Stmt.copyPropList (acc.copyProp m).2 stmts).2 := by
  induction stmts generalizing acc m with
  | nil => simp [List.foldl, Stmt.copyPropList]
  | cons s ss ih =>
    simp only [List.foldl, Stmt.copyPropList]
    rw [ih]; simp only [Stmt.copyProp]

private theorem copyProp_foldl_skip_snd (m : CopyMap) (stmts : List Stmt) :
    ((stmts.foldl (init := Stmt.skip) (· ;; ·)).copyProp m).2 =
    (Stmt.copyPropList m stmts).2 := by
  have := copyProp_foldl_seq_snd m Stmt.skip stmts
  simp [Stmt.copyProp] at this; exact this

/-! ## Statement Copy Propagation Correctness -/

-- Helper for repeated assign non-var pattern
private theorem assign_nonvar_correct (m : CopyMap) (x : String) (e : Expr) (v : Value)
    (σ σ' : PState) (he : e.eval σ = some v) (hs : σ.setVar x v = some σ')
    (hm : m.agrees σ) :
    BigStep σ (.assign x (Expr.copyProp m e)) (.normal σ') ∧
    CopyMap.agrees (m.erase x |>.filter fun _ v => v != x) σ' :=
  ⟨BigStep.assign (by rw [Expr.copyProp_eval m e σ hm]; exact he) hs,
   agrees_after_erase_filter m x σ σ' hm (fun z hz => PState.getVar_setVar_ne hs hz)⟩

theorem Stmt.copyProp_correct' (m : CopyMap) (h : BigStep σ s r) (hm : m.agrees σ) :
    BigStep σ (s.copyProp m).1 r ∧
    (∀ σ', r = .normal σ' → (s.copyProp m).2.agrees σ') := by
  induction h generalizing m with
  | skip =>
    simp only [Stmt.copyProp]
    exact ⟨BigStep.skip, fun _ h => by cases h; exact hm⟩
  | assign he hs =>
    rename_i v σ' σ0 x e
    match e with
    | .var y =>
      simp only [Stmt.copyProp]
      have heval : σ0.getVar y = some v := by simpa [Expr.eval] using he
      constructor
      · exact BigStep.assign
          (by simp only [Expr.eval]; rw [getVar_copyProp_var m y σ0 hm]; exact heval) hs
      · intro σ'' heq; cases heq
        exact agrees_after_assign_var m x y _ _ _ hm heval
          (PState.getVar_setVar_eq hs) (fun z hz => PState.getVar_setVar_ne hs hz)
    | .lit _ => simp only [Stmt.copyProp]; exact assign_nonvar_correct m x _ v σ0 σ' he hs hm
              |>.imp id (fun h => fun σ'' heq => by cases heq; exact h)
    | .binop .. => simp only [Stmt.copyProp]; exact assign_nonvar_correct m x _ v σ0 σ' he hs hm
              |>.imp id (fun h => fun σ'' heq => by cases heq; exact h)
    | .unop .. => simp only [Stmt.copyProp]; exact assign_nonvar_correct m x _ v σ0 σ' he hs hm
              |>.imp id (fun h => fun σ'' heq => by cases heq; exact h)
    | .arrGet .. => simp only [Stmt.copyProp]; exact assign_nonvar_correct m x _ v σ0 σ' he hs hm
              |>.imp id (fun h => fun σ'' heq => by cases heq; exact h)
    | .arrLen .. => simp only [Stmt.copyProp]; exact assign_nonvar_correct m x _ v σ0 σ' he hs hm
              |>.imp id (fun h => fun σ'' heq => by cases heq; exact h)
    | .strLen .. => simp only [Stmt.copyProp]; exact assign_nonvar_correct m x _ v σ0 σ' he hs hm
              |>.imp id (fun h => fun σ'' heq => by cases heq; exact h)
    | .strGet .. => simp only [Stmt.copyProp]; exact assign_nonvar_correct m x _ v σ0 σ' he hs hm
              |>.imp id (fun h => fun σ'' heq => by cases heq; exact h)
  | decl he hs =>
    simp only [Stmt.copyProp]
    constructor
    · exact BigStep.decl (by rw [Expr.copyProp_eval m _ _ hm]; exact he) hs
    · intro σ'' heq; cases heq
      exact agrees_after_erase_filter m _ _ _ hm
        (fun z hz => PState.getVar_setVar_ne hs hz)
  | seqNormal h₁ h₂ ih₁ ih₂ =>
    simp only [Stmt.copyProp]
    have ⟨hbs₁, hag₁⟩ := ih₁ m hm
    have ⟨hbs₂, hag₂⟩ := ih₂ _ (hag₁ _ rfl)
    exact ⟨BigStep.seqNormal hbs₁ hbs₂, hag₂⟩
  | seqReturn h₁ ih₁ =>
    simp only [Stmt.copyProp]
    have ⟨hbs₁, _⟩ := ih₁ m hm
    exact ⟨BigStep.seqReturn hbs₁, fun _ h => by cases h⟩
  | ifTrue hc _ ih =>
    simp only [Stmt.copyProp]
    have ⟨hbs, _⟩ := ih m hm
    constructor
    · exact BigStep.ifTrue (by rw [Expr.copyProp_eval m _ _ hm]; exact hc) hbs
    · intro σ' heq; cases heq; exact CopyMap.agrees_empty _
  | ifFalse hc _ ih =>
    simp only [Stmt.copyProp]
    have ⟨hbs, _⟩ := ih m hm
    constructor
    · exact BigStep.ifFalse (by rw [Expr.copyProp_eval m _ _ hm]; exact hc) hbs
    · intro σ' heq; cases heq; exact CopyMap.agrees_empty _
  | @whileTrue σ₁ b σ₂ e r hc hb hw ihb ihw =>
    simp only [Stmt.copyProp]
    have hem₁ := CopyMap.agrees_empty σ₁
    have hem₂ := CopyMap.agrees_empty σ₂
    have ⟨hbs_b, _⟩ := ihb {} hem₁
    have ⟨hbs_w, _⟩ := ihw {} hem₂
    constructor
    · exact BigStep.whileTrue
        (by rw [Expr.copyProp_eval {} _ _ hem₁]; exact hc) hbs_b hbs_w
    · intro σ' heq; cases heq; exact CopyMap.agrees_empty _
  | @whileReturn σ₁ b e v σ₂ hc hb ihb =>
    simp only [Stmt.copyProp]
    have hem := CopyMap.agrees_empty σ₁
    have ⟨hbs_b, _⟩ := ihb {} hem
    constructor
    · exact BigStep.whileReturn
        (by rw [Expr.copyProp_eval {} _ _ hem]; exact hc) hbs_b
    · intro σ' heq; cases heq
  | whileFalse hc =>
    simp only [Stmt.copyProp]
    constructor
    · exact BigStep.whileFalse
        (by rw [Expr.copyProp_eval {} _ _ (CopyMap.agrees_empty _)]; exact hc)
    · intro σ' heq; cases heq; exact CopyMap.agrees_empty _
  | alloc hsz ha hs =>
    simp only [Stmt.copyProp]
    constructor
    · exact BigStep.alloc (by rw [Expr.copyProp_eval m _ _ hm]; exact hsz) ha hs
    · intro σ'' heq; cases heq
      -- hs : {frames := σ✝.frames, heap := heap'✝, funs := σ✝.funs}.setVar x✝ ... = some σ'✝
      -- getVar on the modified state equals getVar on σ✝ (only frames matter)
      exact agrees_after_erase_filter m _ _ _ hm
        (fun z hz => by have := PState.getVar_setVar_ne hs hz; exact this)
  | free he hf =>
    simp only [Stmt.copyProp]
    exact ⟨BigStep.free (by rw [Expr.copyProp_eval m _ _ hm]; exact he) hf,
           fun σ' heq => by cases heq; exact hm⟩
  | arrSet harr hidx hval hw =>
    simp only [Stmt.copyProp]
    exact ⟨BigStep.arrSet
            (by rw [Expr.copyProp_eval m _ _ hm]; exact harr)
            (by rw [Expr.copyProp_eval m _ _ hm]; exact hidx)
            (by rw [Expr.copyProp_eval m _ _ hm]; exact hval) hw,
           fun σ' heq => by cases heq; exact hm⟩
  | ret he =>
    simp only [Stmt.copyProp]
    exact ⟨BigStep.ret (by rw [Expr.copyProp_eval m _ _ hm]; exact he),
           fun σ' heq => by cases heq⟩
  | block hb ih =>
    simp only [Stmt.copyProp]
    have ⟨hbs, hag⟩ := ih m hm
    constructor
    · apply BigStep.block; rw [← copyProp_foldl_skip_fst]; exact hbs
    · intro σ' heq; cases heq
      have hag' := hag _ rfl
      rw [copyProp_foldl_skip_snd] at hag'; exact hag'
  | callStmt hlook hargs hparams hframe hbody hpop ih =>
    simp only [Stmt.copyProp]
    constructor
    · exact BigStep.callStmt hlook
        (by rw [Expr.copyPropList_mapM_eval m _ _ hm]; exact hargs)
        hparams hframe hbody hpop
    · intro σ' heq; cases heq; exact CopyMap.agrees_empty _
  | scope hargs hlen hframe hbody hpop ih_body =>
    simp only [Stmt.copyProp]
    constructor
    · exact BigStep.scope
        (by rw [Expr.copyPropList_mapM_eval m _ _ hm]; exact hargs)
        hlen hframe
        ((ih_body {} (CopyMap.agrees_empty _)).1)
        hpop
    · intro σ' heq; cases heq; exact CopyMap.agrees_empty _

/-- Copy propagation preserves big-step semantics. -/
theorem Stmt.copyProp_correct (h : BigStep σ s r) :
    BigStep σ s.copyPropagation r := by
  unfold Stmt.copyPropagation
  exact (Stmt.copyProp_correct' {} h (CopyMap.agrees_empty σ)).1

end Radix
