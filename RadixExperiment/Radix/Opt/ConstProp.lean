/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Opt.ConstFold
import Std.Data.HashMap

/-! # Constant Propagation

Track which variables hold known constant values and substitute them.
Unlike constant folding (which only simplifies literal subexpressions),
constant propagation tracks the flow of constants through assignments:
`x := 5; y := x + 1` becomes `x := 5; y := 6` after propagation + folding.

The `ConstMap` records which variables are known to hold specific values.
Like copy propagation, the map is reset at control flow joins. After
substitution, constant folding is applied to maximize simplification.

The correctness proof follows the same pattern as copy propagation:
maintain a `ConstMap.agrees` invariant and show it holds after each
statement form.
-/

namespace Radix
open Std

abbrev ConstMap := HashMap String Value

/-- Substitute known constants in an expression. -/
def Expr.constProp (m : ConstMap) : Expr → Expr
  | .lit v => .lit v
  | .var x => match m.get? x with
    | some v => .lit v
    | none => .var x
  | .binop op l r => .binop op (l.constProp m) (r.constProp m)
  | .unop op e => .unop op (e.constProp m)
  | .arrGet arr idx => .arrGet (arr.constProp m) (idx.constProp m)
  | .arrLen arr => .arrLen (arr.constProp m)
  | .strLen s => .strLen (s.constProp m)
  | .strGet s idx => .strGet (s.constProp m) (idx.constProp m)

def Expr.constPropList (m : ConstMap) (es : List Expr) : List Expr :=
  es.map (Expr.constProp m)

mutual
/-- Constant propagation on statements, maintaining a map of known constants.
Also applies constant folding after substitution. -/
def Stmt.constProp (m : ConstMap) : Stmt → Stmt × ConstMap
  | .skip => (.skip, m)
  | .assign x e =>
    let e' := (Expr.constProp m e).constFold
    match e' with
    | .lit v => (.assign x e', m.insert x v)
    | _ => (.assign x e', m.erase x)
  | .seq s₁ s₂ =>
    let (s₁', m₁) := s₁.constProp m
    let (s₂', m₂) := s₂.constProp m₁
    (.seq s₁' s₂', m₂)
  | .ite c t f =>
    let c' := (Expr.constProp m c).constFold
    match c' with
    | .lit (.bool true) =>
      let (t', m') := t.constProp m
      (t', m')
    | .lit (.bool false) =>
      let (f', m') := f.constProp m
      (f', m')
    | _ =>
      let (t', _) := t.constProp m
      let (f', _) := f.constProp m
      (.ite c' t' f', {})
  | .while c b =>
    let c' := (Expr.constProp {} c).constFold
    let (b', _) := b.constProp {}
    (.while c' b', {})
  | .decl x ty e =>
    let e' := (Expr.constProp m e).constFold
    match e' with
    | .lit v => (.decl x ty e', m.insert x v)
    | _ => (.decl x ty e', m.erase x)
  | .alloc x ty sz =>
    let sz' := (Expr.constProp m sz).constFold
    (.alloc x ty sz', m.erase x)
  | .free e => (.free (Expr.constProp m e), m)
  | .arrSet arr idx val =>
    (.arrSet (Expr.constProp m arr) (Expr.constProp m idx) (Expr.constProp m val), m)
  | .ret e => (.ret ((Expr.constProp m e).constFold), m)
  | .block stmts =>
    let (stmts', m') := Stmt.constPropList m stmts
    (.block stmts', m')
  | .callStmt f args =>
    (.callStmt f (Expr.constPropFoldList m args), {})
  | .scope ps as body =>
    (.scope ps (Expr.constPropFoldList m as) (body.constProp {}).1, {})

def Stmt.constPropList (m : ConstMap) : List Stmt → List Stmt × ConstMap
  | [] => ([], m)
  | s :: ss =>
    let (s', m') := s.constProp m
    let (ss', m'') := Stmt.constPropList m' ss
    (s' :: ss', m'')

def Expr.constPropFoldList (m : ConstMap) : List Expr → List Expr
  | [] => []
  | e :: es => (e.constProp m).constFold :: Expr.constPropFoldList m es
end

def Stmt.constPropagation (s : Stmt) : Stmt :=
  (s.constProp {}).1

/-! ## Map Agreement Invariant -/

/-- The constant map agrees with a state if every recorded constant `x -> v`
holds at runtime: variable `x` contains exactly value `v`. -/
def ConstMap.agrees (m : ConstMap) (σ : PState) : Prop :=
  ∀ x v, m.get? x = some v → σ.getVar x = some v

theorem ConstMap.agrees_empty (σ : PState) : ({} : ConstMap).agrees σ :=
  fun x v h => absurd (show ({} : ConstMap)[x]? = some v from h) (by simp)

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

private theorem PState.getVar_mk_eq_getVar (σ : PState) (h' : Heap) (fns : Std.HashMap String FunDecl)
    (x : String) :
    (PState.mk σ.frames h' fns).getVar x = σ.getVar x := by
  unfold PState.getVar PState.currentFrame; rfl

/-! ## Expression Constant Propagation Correctness -/

theorem Expr.constProp_eval (m : ConstMap) (e : Expr) (σ : PState) (hm : m.agrees σ) :
    (e.constProp m).eval σ = e.eval σ := by
  induction e with
  | lit v => simp [Expr.constProp, Expr.eval]
  | var x =>
    simp only [Expr.constProp]
    split
    · next v hv => simp [Expr.eval]; exact (hm x v hv).symm
    · rfl
  | binop op l r ihl ihr => simp only [Expr.constProp, Expr.eval, ihl, ihr]
  | unop op e ih => simp only [Expr.constProp, Expr.eval, ih]
  | arrGet arr idx iha ihi => simp only [Expr.constProp, Expr.eval, iha, ihi]
  | arrLen arr ih => simp only [Expr.constProp, Expr.eval, ih]
  | strLen s ih => simp only [Expr.constProp, Expr.eval, ih]
  | strGet s idx ihs ihi => simp only [Expr.constProp, Expr.eval, ihs, ihi]

private theorem Expr.constPropList_mapM_eval (m : ConstMap) (args : List Expr) (σ : PState)
    (hm : m.agrees σ) :
    (Expr.constPropList m args).mapM (Expr.eval σ) = args.mapM (Expr.eval σ) := by
  induction args with
  | nil => simp [Expr.constPropList]
  | cons e es ih =>
    unfold Expr.constPropList
    simp only [List.map_cons, List.mapM_cons, Expr.constProp_eval m e σ hm]
    unfold Expr.constPropList at ih
    rw [ih]

private theorem Expr.constPropFoldList_mapM_eval (m : ConstMap) (args : List Expr) (σ : PState)
    (hm : m.agrees σ) :
    (Expr.constPropFoldList m args).mapM (Expr.eval σ) = args.mapM (Expr.eval σ) := by
  induction args with
  | nil => simp [Expr.constPropFoldList]
  | cons e es ih =>
    simp only [Expr.constPropFoldList, List.mapM_cons,
      Expr.eval_constFold, Expr.constProp_eval m e σ hm, ih]

/-! ## Map Agreement After Assignment -/

private theorem agrees_after_erase
    (m : ConstMap) (x : String) (σ σ' : PState)
    (hm : m.agrees σ)
    (hne : ∀ z, z ≠ x → σ'.getVar z = σ.getVar z) :
    ConstMap.agrees (m.erase x) σ' := by
  intro a v h
  simp [HashMap.getElem?_erase] at h
  obtain ⟨hanx, hav⟩ := h
  have ha : a ≠ x := fun h => hanx (h ▸ rfl)
  rw [hne a ha]; exact hm a v hav

private theorem agrees_after_insert
    (m : ConstMap) (x : String) (v : Value) (σ σ' : PState)
    (hm : m.agrees σ)
    (heqx : σ'.getVar x = some v)
    (hne : ∀ z, z ≠ x → σ'.getVar z = σ.getVar z) :
    ConstMap.agrees (m.insert x v) σ' := by
  intro a w h
  simp [HashMap.getElem?_insert] at h
  by_cases hxa : x = a
  · subst hxa; simp at h; subst h; exact heqx
  · simp [hxa] at h; rw [hne a (Ne.symm hxa)]; exact hm a w h

/-! ## Foldl/ConstPropList Distributivity -/

private theorem constProp_foldl_seq_fst (m : ConstMap) (acc : Stmt) (stmts : List Stmt) :
    ((stmts.foldl (init := acc) (· ;; ·)).constProp m).1 =
    ((Stmt.constPropList (acc.constProp m).2 stmts).1.foldl
      (init := (acc.constProp m).1) (· ;; ·)) := by
  induction stmts generalizing acc m with
  | nil => simp [List.foldl, Stmt.constPropList]
  | cons s ss ih =>
    simp only [List.foldl, Stmt.constPropList]
    rw [ih]; simp only [Stmt.constProp]

private theorem constProp_foldl_skip_fst (m : ConstMap) (stmts : List Stmt) :
    ((stmts.foldl (init := Stmt.skip) (· ;; ·)).constProp m).1 =
    ((Stmt.constPropList m stmts).1.foldl (init := Stmt.skip) (· ;; ·)) := by
  have := constProp_foldl_seq_fst m Stmt.skip stmts
  simp [Stmt.constProp] at this; exact this

private theorem constProp_foldl_seq_snd (m : ConstMap) (acc : Stmt) (stmts : List Stmt) :
    ((stmts.foldl (init := acc) (· ;; ·)).constProp m).2 =
    (Stmt.constPropList (acc.constProp m).2 stmts).2 := by
  induction stmts generalizing acc m with
  | nil => simp [List.foldl, Stmt.constPropList]
  | cons s ss ih =>
    simp only [List.foldl, Stmt.constPropList]
    rw [ih]; simp only [Stmt.constProp]

private theorem constProp_foldl_skip_snd (m : ConstMap) (stmts : List Stmt) :
    ((stmts.foldl (init := Stmt.skip) (· ;; ·)).constProp m).2 =
    (Stmt.constPropList m stmts).2 := by
  have := constProp_foldl_seq_snd m Stmt.skip stmts
  simp [Stmt.constProp] at this; exact this

/-! ## Statement Constant Propagation Correctness -/

theorem Stmt.constProp_correct' (m : ConstMap) (h : BigStep σ s r) (hm : m.agrees σ) :
    BigStep σ (s.constProp m).1 r ∧
    (∀ σ', r = .normal σ' → (s.constProp m).2.agrees σ') := by
  induction h generalizing m with
  | skip =>
    simp only [Stmt.constProp]
    exact ⟨BigStep.skip, fun _ h => by cases h; exact hm⟩
  | assign he hs =>
    rename_i v σ' σ₀ x e
    simp only [Stmt.constProp]
    have he' : (Expr.constProp m e).eval σ₀ = some v := by
      rw [Expr.constProp_eval m e σ₀ hm]; exact he
    have he'' : (Expr.constProp m e).constFold.eval σ₀ = some v := by
      rw [Expr.eval_constFold]; exact he'
    constructor
    · split
      · exact BigStep.assign he'' hs
      · exact BigStep.assign he'' hs
    · intro σ'' heq; cases heq
      split
      · next v' hlit =>
        have hlit' : (Expr.constProp m e).constFold = .lit v' := hlit
        rw [hlit', Expr.eval] at he''
        cases he''
        exact agrees_after_insert m _ _ _ _ hm
          (PState.getVar_setVar_eq hs) (fun z hz => PState.getVar_setVar_ne hs hz)
      · exact agrees_after_erase m _ _ _ hm
          (fun z hz => PState.getVar_setVar_ne hs hz)
  | decl he hs =>
    rename_i v σ' σ₀ x _ty e
    simp only [Stmt.constProp]
    have he' : (Expr.constProp m e).eval σ₀ = some v := by
      rw [Expr.constProp_eval m e σ₀ hm]; exact he
    have he'' : (Expr.constProp m e).constFold.eval σ₀ = some v := by
      rw [Expr.eval_constFold]; exact he'
    constructor
    · split
      · exact BigStep.decl he'' hs
      · exact BigStep.decl he'' hs
    · intro σ'' heq; cases heq
      split
      · next v' hlit =>
        have hlit' : (Expr.constProp m e).constFold = .lit v' := hlit
        rw [hlit', Expr.eval] at he''
        cases he''
        exact agrees_after_insert m _ _ _ _ hm
          (PState.getVar_setVar_eq hs) (fun z hz => PState.getVar_setVar_ne hs hz)
      · exact agrees_after_erase m _ _ _ hm
          (fun z hz => PState.getVar_setVar_ne hs hz)
  | seqNormal h₁ h₂ ih₁ ih₂ =>
    simp only [Stmt.constProp]
    have ⟨hbs₁, hag₁⟩ := ih₁ m hm
    have ⟨hbs₂, hag₂⟩ := ih₂ _ (hag₁ _ rfl)
    exact ⟨BigStep.seqNormal hbs₁ hbs₂, hag₂⟩
  | seqReturn h₁ ih₁ =>
    simp only [Stmt.constProp]
    have ⟨hbs₁, _⟩ := ih₁ m hm
    exact ⟨BigStep.seqReturn hbs₁, fun _ h => by cases h⟩
  | ifTrue hc ht ih =>
    rename_i σ₀ _t _r c _f
    simp only [Stmt.constProp]
    have hc' : (Expr.constProp m c).constFold.eval σ₀ = some (.bool true) := by
      rw [Expr.eval_constFold, Expr.constProp_eval m c σ₀ hm]; exact hc
    split
    · have ⟨hbs, hag⟩ := ih m hm
      exact ⟨hbs, hag⟩
    · next heq =>
        rw [heq, Expr.eval] at hc'; cases hc'
    · have ⟨hbs, _⟩ := ih m hm
      constructor
      · exact BigStep.ifTrue hc' hbs
      · intro σ' heq; cases heq; exact ConstMap.agrees_empty _
  | ifFalse hc hf ih =>
    rename_i σ₀ _f _r c _t
    simp only [Stmt.constProp]
    have hc' : (Expr.constProp m c).constFold.eval σ₀ = some (.bool false) := by
      rw [Expr.eval_constFold, Expr.constProp_eval m c σ₀ hm]; exact hc
    split
    · next heq =>
        rw [heq, Expr.eval] at hc'; cases hc'
    · have ⟨hbs, hag⟩ := ih m hm
      exact ⟨hbs, hag⟩
    · have ⟨hbs, _⟩ := ih m hm
      constructor
      · exact BigStep.ifFalse hc' hbs
      · intro σ' heq; cases heq; exact ConstMap.agrees_empty _
  | @whileTrue σ₁ b σ₂ e r hc hb hw ihb ihw =>
    simp only [Stmt.constProp]
    have hem₁ := ConstMap.agrees_empty σ₁
    have hem₂ := ConstMap.agrees_empty σ₂
    have ⟨hbs_b, _⟩ := ihb {} hem₁
    have ⟨hbs_w, _⟩ := ihw {} hem₂
    constructor
    · exact BigStep.whileTrue
        (by rw [Expr.eval_constFold, Expr.constProp_eval {} _ _ hem₁]; exact hc) hbs_b hbs_w
    · intro σ' heq; cases heq; exact ConstMap.agrees_empty _
  | @whileReturn σ₁ b e v σ₂ hc hb ihb =>
    simp only [Stmt.constProp]
    have hem := ConstMap.agrees_empty σ₁
    have ⟨hbs_b, _⟩ := ihb {} hem
    constructor
    · exact BigStep.whileReturn
        (by rw [Expr.eval_constFold, Expr.constProp_eval {} _ _ hem]; exact hc) hbs_b
    · intro σ' heq; cases heq
  | whileFalse hc =>
    simp only [Stmt.constProp]
    constructor
    · exact BigStep.whileFalse
        (by rw [Expr.eval_constFold, Expr.constProp_eval {} _ _ (ConstMap.agrees_empty _)]; exact hc)
    · intro σ' heq; cases heq; exact ConstMap.agrees_empty _
  | alloc hsz ha hs =>
    simp only [Stmt.constProp]
    constructor
    · exact BigStep.alloc
        (by rw [Expr.eval_constFold, Expr.constProp_eval m _ _ hm]; exact hsz) ha hs
    · intro σ'' heq; cases heq
      exact agrees_after_erase m _ _ _ hm
        (fun z hz => by
          rw [PState.getVar_setVar_ne hs hz, PState.getVar_mk_eq_getVar])
  | free he hf =>
    simp only [Stmt.constProp]
    exact ⟨BigStep.free (by rw [Expr.constProp_eval m _ _ hm]; exact he) hf,
           fun σ' heq => by cases heq; exact hm⟩
  | arrSet harr hidx hval hw =>
    simp only [Stmt.constProp]
    exact ⟨BigStep.arrSet
            (by rw [Expr.constProp_eval m _ _ hm]; exact harr)
            (by rw [Expr.constProp_eval m _ _ hm]; exact hidx)
            (by rw [Expr.constProp_eval m _ _ hm]; exact hval) hw,
           fun σ' heq => by cases heq; exact hm⟩
  | ret he =>
    simp only [Stmt.constProp]
    exact ⟨BigStep.ret (by rw [Expr.eval_constFold, Expr.constProp_eval m _ _ hm]; exact he),
           fun σ' heq => by cases heq⟩
  | block hb ih =>
    simp only [Stmt.constProp]
    have ⟨hbs, hag⟩ := ih m hm
    constructor
    · apply BigStep.block; rw [← constProp_foldl_skip_fst]; exact hbs
    · intro σ' heq; cases heq
      have hag' := hag _ rfl
      rw [constProp_foldl_skip_snd] at hag'; exact hag'
  | callStmt hlook hargs hparams hframe hbody hpop ih =>
    simp only [Stmt.constProp]
    constructor
    · exact BigStep.callStmt hlook
        (by rw [Expr.constPropFoldList_mapM_eval m _ _ hm]; exact hargs)
        hparams hframe hbody hpop
    · intro σ' heq; cases heq; exact ConstMap.agrees_empty _
  | scope hargs hlen hframe hbody hpop ih_body =>
    simp only [Stmt.constProp]
    constructor
    · exact BigStep.scope
        (by rw [Expr.constPropFoldList_mapM_eval m _ _ hm]; exact hargs)
        hlen hframe
        ((ih_body {} (ConstMap.agrees_empty _)).1)
        hpop
    · intro σ' heq; cases heq; exact ConstMap.agrees_empty _

/-- Constant propagation preserves big-step semantics. -/
theorem Stmt.constPropagation_correct (h : BigStep σ s r) :
    BigStep σ s.constPropagation r := by
  unfold Stmt.constPropagation
  exact (Stmt.constProp_correct' {} h (ConstMap.agrees_empty σ)).1

end Radix
