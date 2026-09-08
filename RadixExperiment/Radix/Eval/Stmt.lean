/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Expr
import Radix.Eval.IO

/-! # Radix Big-Step Semantics

Relational big-step semantics for statements, including function call/return.

This is the reference semantics against which all optimizations are verified.
Each optimization proves: if `BigStep sigma s r`, then `BigStep sigma (s.opt) r`.
The `BigStep.det` theorem (`Radix.Proofs.Determinism`) shows that this relation
is deterministic, so the original and optimized programs are observationally
equivalent.

The semantics uses `StmtResult` to distinguish normal completion, early
return, and explicit rejection. The `seqReturn` rule short-circuits: if the first statement in a
sequence returns, the second is never executed.
-/

namespace Radix

/-- Result of executing a statement: normal completion, ordinary return, or rejection. -/
inductive StmtResult where
  | normal : PState → StmtResult
  | returned : Value → PState → StmtResult
  | rejected : PState → StmtResult

/-- Extract the state from a result. -/
def StmtResult.state : StmtResult → PState
  | .normal σ => σ
  | .returned _ σ => σ
  | .rejected σ => σ

def StmtResult.afterCall (r : StmtResult) (σ : PState) : StmtResult :=
  match r with
  | .rejected _ => .rejected σ
  | _ => .normal σ

/-- Big-step operational semantics for Radix statements.

Notation: `⟨sigma, s⟩ ⇓ r` means statement `s` in state `sigma` produces
result `r`. The relation is deterministic (`BigStep.det`). Faults have no derivation;
well-typed expressions can still fault, so typing alone does not imply progress. -/
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

  | seqReject (h₁ : BigStep σ₁ s₁ (.rejected σ₂)) :
    BigStep σ₁ (s₁ ;; s₂) (.rejected σ₂)

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

  | whileReject (hc : e.eval σ₁ = some (.bool true))
      (hb : BigStep σ₁ b (.rejected σ₂)) :
    BigStep σ₁ (.while e b) (.rejected σ₂)

  | whileFalse (hc : e.eval σ = some (.bool false)) :
    BigStep σ (.while e b) (.normal σ)

  | alloc (hsz : szExpr.eval σ = some (.uint64 sz))
      (ha : σ.heap.alloc (Array.replicate sz.toNat (.uint64 0)) = (a, heap'))
      (hs : { σ with heap := heap' }.setVar x (.addr a) = some σ') :
    BigStep σ (.alloc x _ty szExpr) (.normal σ')

  | reject : BigStep σ .reject (.rejected σ)

  | readU64 (hr : ByteIO.readU64 σ.input σ.cursor = (some n, cursor))
      (hs : ({ σ with cursor }).setVar x (.uint64 n) = some σ') :
    BigStep σ (.readU64 x) (.normal σ')

  | readReject (hr : ByteIO.readU64 σ.input σ.cursor = (none, cursor)) :
    BigStep σ (.readU64 x) (.rejected { σ with cursor })

  | writeU64 (he : e.eval σ = some (.uint64 n)) :
    BigStep σ (.writeU64 e) (.normal { σ with output := σ.output ++ ByteIO.writeU64 n })

  | writeText :
    BigStep σ (.writeText text) (.normal { σ with output := σ.output ++ text.toUTF8 })

  | expectEof (he : ByteIO.skipWhitespace σ.input σ.cursor = σ.input.size) :
    BigStep σ .expectEof (.normal { σ with cursor := σ.input.size })

  | eofReject (he : ByteIO.skipWhitespace σ.input σ.cursor ≠ σ.input.size) :
    BigStep σ .expectEof (.rejected { σ with cursor := ByteIO.skipWhitespace σ.input σ.cursor })

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
    BigStep σ (.callStmt name args) (bodyResult.afterCall σ')

  | scope (hargs : args.mapM (Expr.eval σ) = some vs)
      (hlen : params.length = vs.length)
      (hframe : frame = { env := (params.zip vs).foldl (fun env (p, v) => env.set p.1 v) Env.empty })
      (hbody : BigStep (σ.pushFrame frame) body bodyResult)
      (hpop : bodyResult.state.popFrame = some (fr, σ')) :
    BigStep σ (.scope params args body) (bodyResult.afterCall σ')

set_option quotPrecheck false in
notation:60 "⟨" σ ", " s "⟩" " ⇓ " r:60 => BigStep σ s r

end Radix
