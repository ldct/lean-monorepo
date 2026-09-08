/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Expr

/-! # Radix Big-Step Semantics

Relational big-step semantics for statements, including function call/return.

This is the reference semantics against which all optimizations are verified.
Each optimization proves: if `BigStep sigma s r`, then `BigStep sigma (s.opt) r`.
The `BigStep.det` theorem (`Radix.Proofs.Determinism`) shows that this relation
is deterministic, so the original and optimized programs are observationally
equivalent.

The semantics uses `StmtResult` to distinguish normal completion from early
return. The `seqReturn` rule short-circuits: if the first statement in a
sequence returns, the second is never executed.
-/

namespace Radix

/-- Result of executing a statement: either normal completion or a return. -/
inductive StmtResult where
  | normal : PState → StmtResult
  | returned : Value → PState → StmtResult

/-- Extract the state from a result. -/
def StmtResult.state : StmtResult → PState
  | .normal σ => σ
  | .returned _ σ => σ

/-- Big-step operational semantics for Radix statements.

Notation: `⟨sigma, s⟩ ⇓ r` means statement `s` in state `sigma` produces
result `r`. The relation is deterministic (`BigStep.det`) and total for
well-typed, terminating programs. -/
inductive BigStep : PState → Stmt → StmtResult → Prop where
  | skip :
    BigStep σ .skip (.normal σ)

  | assign (he : e.eval σ = some v) (hs : σ.setVar x v = some σ') :
    BigStep σ (.assign x e) (.normal σ')

  | decl (he : e.eval σ = some v) (hs : σ.setVar x v = some σ') :
    BigStep σ (.decl x _ty e) (.normal σ')

  | seqNormal (h₁ : BigStep σ₁ s₁ (.normal σ₂)) (h₂ : BigStep σ₂ s₂ r) :
    BigStep σ₁ (s₁ ;; s₂) r

  | seqReturn (h₁ : BigStep σ₁ s₁ (.returned v σ₂)) :
    BigStep σ₁ (s₁ ;; s₂) (.returned v σ₂)

  | ifTrue (hc : e.eval σ = some (.bool true)) (ht : BigStep σ t r) :
    BigStep σ (.ite e t f) r

  | ifFalse (hc : e.eval σ = some (.bool false)) (hf : BigStep σ f r) :
    BigStep σ (.ite e t f) r

  | whileTrue (hc : e.eval σ₁ = some (.bool true))
      (hb : BigStep σ₁ b (.normal σ₂))
      (hw : BigStep σ₂ (.while e b) r) :
    BigStep σ₁ (.while e b) r

  | whileReturn (hc : e.eval σ₁ = some (.bool true))
      (hb : BigStep σ₁ b (.returned v σ₂)) :
    BigStep σ₁ (.while e b) (.returned v σ₂)

  | whileFalse (hc : e.eval σ = some (.bool false)) :
    BigStep σ (.while e b) (.normal σ)

  | alloc (hsz : szExpr.eval σ = some (.uint64 sz))
      (ha : σ.heap.alloc (Array.replicate sz.toNat (.uint64 0)) = (a, heap'))
      (hs : (PState.mk σ.frames heap' σ.funs).setVar x (.addr a) = some σ') :
    BigStep σ (.alloc x _ty szExpr) (.normal σ')

  | free (he : e.eval σ = some (.addr a)) (hf : σ.heap.free a = some heap') :
    BigStep σ (.free e) (.normal { σ with heap := heap' })

  | arrSet (harr : arr.eval σ = some (.addr a))
      (hidx : idx.eval σ = some (.uint64 i))
      (hval : val.eval σ = some v)
      (hw : σ.heap.write a i.toNat v = some heap') :
    BigStep σ (.arrSet arr idx val) (.normal { σ with heap := heap' })

  | ret (he : e.eval σ = some v) :
    BigStep σ (.ret e) (.returned v σ)

  | block (hb : BigStep σ (stmts.foldl (init := Stmt.skip) (· ;; ·)) r) :
    BigStep σ (.block stmts) r

  | callStmt (hlook : σ.lookupFun name = some fd)
      (hargs : args.mapM (Expr.eval σ) = some vs)
      (hparams : fd.params.length = vs.length)
      (hframe : frame = { env := (fd.params.zip vs).foldl (fun env (p, v) => env.set p.1 v) Env.empty })
      (hbody : BigStep (σ.pushFrame frame) fd.body bodyResult)
      (hpop : bodyResult.state.popFrame = some (fr, σ')) :
    BigStep σ (.callStmt name args) (.normal σ')

  | scope (hargs : args.mapM (Expr.eval σ) = some vs)
      (hlen : params.length = vs.length)
      (hframe : frame = { env := (params.zip vs).foldl (fun env (p, v) => env.set p.1 v) Env.empty })
      (hbody : BigStep (σ.pushFrame frame) body bodyResult)
      (hpop : bodyResult.state.popFrame = some (fr, σ')) :
    BigStep σ (.scope params args body) (.normal σ')

set_option quotPrecheck false in
notation:60 "⟨" σ ", " s "⟩" " ⇓ " r:60 => BigStep σ s r

end Radix
