/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Stmt
import Std.Data.HashMap

/-! # Function Inlining

Inline small, non-recursive functions at their call sites. A `callStmt`
is replaced by a `scope` that pushes a fresh frame with the function's
parameters bound to the argument expressions, executes the (recursively
inlined) body, then pops the frame.

Inlining criteria:
- Body size at most `inlineThreshold` (currently 10)
- No recursive calls (`containsCall` check)
- Bounded inlining depth to ensure termination

The correctness proof (`Stmt.inline_correct`) requires an auxiliary
invariant `hfuns : sigma.funs = funs` to ensure the static function
table used for inlining matches the runtime function table. The
`BigStep.funs_preserved` theorem establishes that `funs` is never
modified during execution.
-/

namespace Radix
open Std

mutual
/-- Rough measure of statement size for inlining heuristics. -/
def Stmt.size : Stmt → Nat
  | .skip => 0
  | .assign _ _ => 1
  | .seq s₁ s₂ => s₁.size + s₂.size
  | .ite _ t f => 1 + t.size + f.size
  | .while _ b => 1 + b.size
  | .decl _ _ _ => 1
  | .alloc _ _ _ => 1
  | .free _ => 1
  | .arrSet _ _ _ => 1
  | .ret _ => 1
  | .block stmts => Stmt.sizeList stmts
  | .callStmt _ _ => 1
  | .scope _ _ body => 1 + body.size

def Stmt.sizeList : List Stmt → Nat
  | [] => 0
  | s :: ss => s.size + Stmt.sizeList ss
end

/-- Maximum size for a function body to be considered for inlining. -/
def inlineThreshold : Nat := 10

mutual
/-- Check if a statement contains a call to a specific function (prevent recursive inlining). -/
def Stmt.containsCall (name : String) : Stmt → Bool
  | .skip | .assign _ _ | .decl _ _ _ | .alloc _ _ _ | .free _
  | .arrSet _ _ _ | .ret _ => false
  | .seq s₁ s₂ => s₁.containsCall name || s₂.containsCall name
  | .ite _ t f => t.containsCall name || f.containsCall name
  | .while _ b => b.containsCall name
  | .block stmts => Stmt.containsCallList name stmts
  | .callStmt f _ => f == name
  | .scope _ _ body => body.containsCall name

def Stmt.containsCallList (name : String) : List Stmt → Bool
  | [] => false
  | s :: ss => s.containsCall name || Stmt.containsCallList name ss
end

/-- Substitute variables in an expression. -/
def Expr.substVars (params : List String) (args : List Expr) : Expr → Expr
  | .lit v => .lit v
  | .var x =>
    match params.zip args |>.find? (·.1 == x) with
    | some (_, e) => e
    | none => .var x
  | .binop op l r => .binop op (l.substVars params args) (r.substVars params args)
  | .unop op e => .unop op (e.substVars params args)
  | .arrGet a i => .arrGet (a.substVars params args) (i.substVars params args)
  | .arrLen a => .arrLen (a.substVars params args)
  | .strLen s => .strLen (s.substVars params args)
  | .strGet s i => .strGet (s.substVars params args) (i.substVars params args)

def Expr.substVarsList (params : List String) (args : List Expr) (es : List Expr) : List Expr :=
  es.map (Expr.substVars params args)

mutual
/-- Substitute parameter names with argument expressions in a statement body. -/
def Stmt.substParams (params : List String) (args : List Expr) : Stmt → Stmt
  | .skip => .skip
  | .assign x e => .assign x (Expr.substVars params args e)
  | .seq s₁ s₂ => .seq (s₁.substParams params args) (s₂.substParams params args)
  | .ite c t f => .ite (Expr.substVars params args c)
      (t.substParams params args) (f.substParams params args)
  | .while c b => .while (Expr.substVars params args c) (b.substParams params args)
  | .decl x ty e => .decl x ty (Expr.substVars params args e)
  | .alloc x ty sz => .alloc x ty (Expr.substVars params args sz)
  | .free e => .free (Expr.substVars params args e)
  | .arrSet a i v => .arrSet (Expr.substVars params args a) (Expr.substVars params args i)
      (Expr.substVars params args v)
  | .ret e => .ret (Expr.substVars params args e)
  | .block stmts => .block (Stmt.substParamsList params args stmts)
  | .callStmt f as => .callStmt f (Expr.substVarsList params args as)
  | .scope ps as body => .scope ps (Expr.substVarsList params args as) (body.substParams params args)

def Stmt.substParamsList (params : List String) (args : List Expr) : List Stmt → List Stmt
  | [] => []
  | s :: ss => s.substParams params args :: Stmt.substParamsList params args ss
end

mutual
/-- Inline small function calls in a statement.
    The `depth` parameter bounds the inlining depth, ensuring termination:
    `depth` decreases in the `callStmt` case (where we recurse on the inlined body),
    and the statement decreases structurally in all other cases. -/
def Stmt.inline (funs : HashMap String FunDecl) (depth : Nat) : Stmt → Stmt
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq s₁ s₂ => .seq (s₁.inline funs depth) (s₂.inline funs depth)
  | .ite c t f => .ite c (t.inline funs depth) (f.inline funs depth)
  | .while c b => .while c (b.inline funs depth)
  | .decl x ty e => .decl x ty e
  | .alloc x ty sz => .alloc x ty sz
  | .free e => .free e
  | .arrSet a i v => .arrSet a i v
  | .ret e => .ret e
  | .block stmts => .block (Stmt.inlineList funs depth stmts)
  | .callStmt name args =>
    match depth with
    | 0 => .callStmt name args
    | depth' + 1 =>
      match funs.get? name with
      | some fd =>
        if fd.body.size ≤ inlineThreshold && !fd.body.containsCall name then
          .scope fd.params args (fd.body.inline funs depth')
        else
          .callStmt name args
      | none => .callStmt name args
  | .scope ps as body => .scope ps as (body.inline funs depth)

def Stmt.inlineList (funs : HashMap String FunDecl) (depth : Nat) : List Stmt → List Stmt
  | [] => []
  | s :: ss => s.inline funs depth :: Stmt.inlineList funs depth ss
end

-- Helper: inline distributes over seq-foldl
theorem Stmt.inline_foldl_seq (funs : HashMap String FunDecl) (depth : Nat)
    (acc : Stmt) (stmts : List Stmt) :
    (stmts.foldl (init := acc) (· ;; ·)).inline funs depth =
    (stmts.map (Stmt.inline funs depth)).foldl (init := acc.inline funs depth) (· ;; ·) := by
  induction stmts generalizing acc with
  | nil => simp [List.foldl, List.map]
  | cons s ss ih =>
    simp only [List.foldl, List.map]
    rw [ih (acc ;; s)]
    simp only [Stmt.inline]

-- Helper: inlineList is map of inline
theorem Stmt.inlineList_eq_map (funs : HashMap String FunDecl) (depth : Nat) (stmts : List Stmt) :
    Stmt.inlineList funs depth stmts = stmts.map (Stmt.inline funs depth) := by
  induction stmts with
  | nil => simp [Stmt.inlineList, List.map]
  | cons s ss ih =>
    simp only [Stmt.inlineList, List.map]
    exact congrArg _ ih

-- Helper: PState.funs is preserved by updateCurrentFrame
private theorem PState.updateCurrentFrame_funs {σ : PState} {f : Frame → Frame} {σ' : PState}
    (h : σ.updateCurrentFrame f = some σ') : σ'.funs = σ.funs := by
  cases σ with | mk frames heap funs =>
  unfold PState.updateCurrentFrame at h
  cases frames with
  | nil => exact absurd h nofun
  | cons fr rest => simp at h; subst h; rfl

private theorem PState.setVar_funs {σ : PState} {x : String} {v : Value} {σ' : PState}
    (h : σ.setVar x v = some σ') : σ'.funs = σ.funs :=
  PState.updateCurrentFrame_funs h

private theorem PState.popFrame_funs {σ : PState} {fr : Frame} {σ' : PState}
    (h : σ.popFrame = some (fr, σ')) : σ'.funs = σ.funs := by
  cases σ with | mk frames heap funs =>
  unfold PState.popFrame at h
  cases frames with
  | nil => exact absurd h nofun
  | cons _ rest => simp at h; obtain ⟨_, rfl⟩ := h; rfl

/-- The function table is never modified during execution. This invariant
is essential for inlining correctness: it ensures the static function
table used to decide what to inline matches the runtime table. -/
theorem BigStep.funs_preserved (h : BigStep σ s r) : r.state.funs = σ.funs := by
  induction h with
  | skip => rfl
  | assign _ hs => exact PState.setVar_funs hs
  | decl _ hs => exact PState.setVar_funs hs
  | seqNormal _ _ ih₁ ih₂ =>
    simp only [StmtResult.state] at ih₁; rw [ih₂, ih₁]
  | seqReturn _ ih₁ => exact ih₁
  | ifTrue _ _ ih => exact ih
  | ifFalse _ _ ih => exact ih
  | whileTrue _ _ _ ihb ihw =>
    simp only [StmtResult.state] at ihb; rw [ihw, ihb]
  | whileReturn _ _ ih => exact ih
  | whileFalse _ => rfl
  | alloc _ _ hs => have h := PState.setVar_funs hs; exact h
  | free _ _ => rfl
  | arrSet _ _ _ _ => rfl
  | ret _ => rfl
  | block _ ih => exact ih
  | callStmt _ _ _ _ _ hpop ih_body =>
    simp only [StmtResult.state]
    rw [PState.popFrame_funs hpop, ih_body]; rfl
  | scope _ _ _ _ hpop ih_body =>
    simp only [StmtResult.state]
    rw [PState.popFrame_funs hpop, ih_body]; rfl

/-- Inlining preserves big-step semantics at any inlining depth.
The `hfuns` hypothesis ties the static function table to the runtime one. -/
theorem Stmt.inline_correct {funs : HashMap String FunDecl}
    (h : BigStep σ s r) (hfuns : σ.funs = funs) :
    ∀ depth, BigStep σ (s.inline funs depth) r := by
  induction h with
  | skip => intro; simp only [Stmt.inline]; exact .skip
  | assign he hs => intro; simp only [Stmt.inline]; exact .assign he hs
  | decl he hs => intro; simp only [Stmt.inline]; exact .decl he hs
  | seqNormal h₁ h₂ ih₁ ih₂ =>
    intro depth; simp only [Stmt.inline]
    exact .seqNormal (ih₁ hfuns depth) (ih₂ ((BigStep.funs_preserved h₁).trans hfuns) depth)
  | seqReturn h₁ ih₁ =>
    intro depth; simp only [Stmt.inline]; exact .seqReturn (ih₁ hfuns depth)
  | ifTrue hc ht ih =>
    intro depth; simp only [Stmt.inline]; exact .ifTrue hc (ih hfuns depth)
  | ifFalse hc hf ih =>
    intro depth; simp only [Stmt.inline]; exact .ifFalse hc (ih hfuns depth)
  | whileTrue hc hb hw ihb ihw =>
    intro depth; simp only [Stmt.inline]
    have ihw' := ihw ((BigStep.funs_preserved hb).trans hfuns)
    simp only [Stmt.inline] at ihw'
    exact .whileTrue hc (ihb hfuns depth) (ihw' depth)
  | whileReturn hc hb ih =>
    intro depth; simp only [Stmt.inline]; exact .whileReturn hc (ih hfuns depth)
  | whileFalse hc =>
    intro; simp only [Stmt.inline]; exact .whileFalse hc
  | alloc hsz ha hs =>
    intro; simp only [Stmt.inline]; exact .alloc hsz ha hs
  | free he hf =>
    intro; simp only [Stmt.inline]; exact .free he hf
  | arrSet harr hidx hval hw =>
    intro; simp only [Stmt.inline]; exact .arrSet harr hidx hval hw
  | ret he =>
    intro; simp only [Stmt.inline]; exact .ret he
  | block hb ih =>
    intro depth; simp only [Stmt.inline]
    apply BigStep.block
    rw [Stmt.inlineList_eq_map]
    have ih' := ih hfuns depth
    rw [Stmt.inline_foldl_seq] at ih'
    simp only [Stmt.inline] at ih'
    exact ih'
  | callStmt hlook hargs hparams hframe hbody hpop ih_body =>
    rename_i fd _ _ _ _ _ _ name _
    intro depth
    match depth with
    | 0 =>
      simp only [Stmt.inline]
      exact .callStmt hlook hargs hparams hframe hbody hpop
    | depth' + 1 =>
      simp only [Stmt.inline]
      have hget : funs.get? name = some fd := by
        rw [← hfuns]; exact hlook
      simp only [hget]
      split
      · exact .scope hargs hparams hframe (ih_body hfuns depth') hpop
      · exact .callStmt hlook hargs hparams hframe hbody hpop
  | scope hargs hlen hframe hbody hpop ih_body =>
    intro depth; simp only [Stmt.inline]
    exact .scope hargs hlen hframe (ih_body hfuns depth) hpop

end Radix
