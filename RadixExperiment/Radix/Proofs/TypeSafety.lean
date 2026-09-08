/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.TypeCheck
import Std.Data.HashMap
import Radix.Eval.Stmt

/-! # Type Safety

Preservation theorem for the Radix type system.

**Preservation** (`Expr.preservation`): if a well-typed expression evaluates
successfully, the result value has the expected type. The proof requires a
heap typing hypothesis (`hheapTy`) stating that heap contents match their
declared element types — standard in type safety proofs for languages with
mutable heap-allocated data.

**Progress** is not included: "a well-typed expression always evaluates to
some value" is false for Radix because `e / 0`, out-of-bounds `arr[i]`, and
out-of-bounds `s[i]` are well-typed but evaluate to `none`. A correct
formulation would require a totality judgment or strengthened preconditions.
-/

namespace Radix
open Std

/-- A value is well-typed if it matches the expected type. -/
def Value.hasType : Value → Ty → Prop
  | .uint64 _, .uint64 => True
  | .bool _,   .bool   => True
  | .unit,     .unit    => True
  | .str _,    .string  => True
  | .addr _,   .array _ => True
  | _, _ => False

/-- Literal values have the type assigned by `typeOf`. -/
private theorem lit_hasType (v : Value) (ty : Ty)
    (hty : Expr.typeOf Γ sigs (.lit v) = some ty) :
    Value.hasType v ty := by
  unfold Expr.typeOf at hty
  cases v <;> simp at hty <;> subst_vars <;> simp [Value.hasType]

/-- Variables in a well-typed environment evaluate to well-typed values. -/
private theorem var_hasType (x : String) (ty : Ty) (v : Value) (σ : PState)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hty : Expr.typeOf Γ sigs (.var x) = some ty)
    (heval : Expr.eval σ (.var x) = some v) :
    Value.hasType v ty := by
  unfold Expr.typeOf at hty; unfold Expr.eval at heval
  have ⟨w, hw, hhas⟩ := henv x ty hty
  simp [hw] at heval; subst heval; exact hhas

/-- Binary operation evaluation preserves types. -/
private theorem BinOp.eval_preserves_type {op : BinOp} {vl vr v : Value} {tl tr ty : Ty}
    (hvl : vl.hasType tl) (hvr : vr.hasType tr)
    (hty : op.typeOfResult tl tr = some ty)
    (hev : op.eval vl vr = some v) :
    v.hasType ty := by
  cases op
  all_goals (first
    | (-- eq and ne: eval works on any values, typeOfResult needs tl == tr
       simp [BinOp.eval] at hev; subst hev
       simp [BinOp.typeOfResult] at hty; obtain ⟨_, rfl⟩ := hty
       simp [Value.hasType])
    | (-- arithmetic without guards (add, sub, mul) and comparisons/logic
       cases tl <;> cases tr <;> simp [BinOp.typeOfResult] at hty
       subst hty
       cases vl <;> simp [Value.hasType] at hvl
       cases vr <;> simp [Value.hasType] at hvr
       simp [BinOp.eval] at hev; subst hev; simp [Value.hasType])
    | (-- div, mod: have an if guard
       cases tl <;> cases tr <;> simp [BinOp.typeOfResult] at hty
       subst hty
       cases vl <;> simp [Value.hasType] at hvl
       cases vr <;> simp [Value.hasType] at hvr
       simp [BinOp.eval] at hev; obtain ⟨_, rfl⟩ := hev; simp [Value.hasType]))

/-- Unary operation evaluation preserves types. -/
private theorem UnaryOp.eval_preserves_type {op : UnaryOp} {v w : Value} {t ty : Ty}
    (hv : v.hasType t)
    (hty : op.typeOfResult t = some ty)
    (hev : op.eval v = some w) :
    w.hasType ty := by
  cases op <;> cases t <;> simp [UnaryOp.typeOfResult] at hty <;>
    subst ty <;> cases v <;> simp [Value.hasType] at hv <;>
    simp [UnaryOp.eval] at hev <;> subst hev <;> simp [Value.hasType]

/-- Type preservation for expressions: if `typeOf` assigns type `ty` to
expression `e`, and `e` evaluates to value `v`, then `v` has type `ty`.

The proof proceeds by structural induction on `e`, delegating to
`BinOp.eval_preserves_type` and `UnaryOp.eval_preserves_type` for
operator cases. The `arrGet` case uses `hheapTy`. -/
theorem Expr.preservation (Γ : TyEnv) (sigs : FunSigs) (σ : PState)
    (e : Expr) (ty : Ty) (v : Value)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hheapTy : ∀ (e : Expr) (a : Addr) (elemTy : Ty),
      Expr.typeOf Γ sigs e = some (.array elemTy) →
      Expr.eval σ e = some (.addr a) →
      ∀ i v, σ.heap.read a i = some v → v.hasType elemTy)
    (hty : Expr.typeOf Γ sigs e = some ty)
    (heval : Expr.eval σ e = some v) :
    Value.hasType v ty := by
  induction e generalizing ty v with
  | lit val =>
    simp [Expr.eval] at heval; subst heval
    exact lit_hasType val ty hty
  | var x => exact var_hasType x ty v σ henv hty heval
  | binop op l r ihl ihr =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases htl : Expr.typeOf Γ sigs l <;> simp [htl] at hty
    rename_i tl
    cases htr : Expr.typeOf Γ sigs r <;> simp [htr] at hty
    rename_i tr
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases hvl : Expr.eval σ l <;> simp [hvl] at heval
    rename_i vl
    cases hvr : Expr.eval σ r <;> simp [hvr] at heval
    rename_i vr
    exact BinOp.eval_preserves_type (ihl tl vl htl hvl) (ihr tr vr htr hvr) hty heval
  | unop op e ih =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases ht : Expr.typeOf Γ sigs e <;> simp [ht] at hty
    rename_i t
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases hw : Expr.eval σ e <;> simp [hw] at heval
    rename_i w
    exact UnaryOp.eval_preserves_type (ih t w ht hw) hty heval
  | arrGet arr idx _ _ =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases h1 : Expr.typeOf Γ sigs arr <;> simp [h1] at hty
    rename_i aty; cases aty <;> simp at hty
    rename_i elemTy
    cases h2 : Expr.typeOf Γ sigs idx <;> simp [h2] at hty
    rename_i ity; cases ity <;> simp at hty; subst ty
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases h3 : Expr.eval σ arr <;> simp [h3] at heval
    rename_i va; cases va <;> simp at heval
    rename_i a
    cases h4 : Expr.eval σ idx <;> simp [h4] at heval
    rename_i vi; cases vi <;> simp at heval
    rename_i i
    exact hheapTy arr a elemTy h1 h3 i.toNat v heval
  | arrLen arr _ =>
    -- typeOf returns .uint64, eval produces .uint64 _
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases h1 : Expr.typeOf Γ sigs arr <;> simp [h1] at hty
    rename_i aty; cases aty <;> simp at hty; subst ty
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases h2 : Expr.eval σ arr <;> simp [h2] at heval
    rename_i va; cases va <;> simp at heval
    rename_i a
    cases h3 : Heap.arraySize σ.heap a <;> simp [h3] at heval
    subst heval; simp [Value.hasType]
  | strLen s _ =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases h1 : Expr.typeOf Γ sigs s <;> simp [h1] at hty
    rename_i st; cases st <;> simp at hty; subst ty
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases h2 : Expr.eval σ s <;> simp [h2] at heval
    rename_i vs; cases vs <;> simp at heval
    subst heval; simp [Value.hasType]
  | strGet s idx _ _ =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases h1 : Expr.typeOf Γ sigs s <;> simp [h1] at hty
    rename_i st; cases st <;> simp at hty
    cases h4 : Expr.typeOf Γ sigs idx <;> simp [h4] at hty
    rename_i it; cases it <;> simp at hty; subst ty
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases h2 : Expr.eval σ s <;> simp [h2] at heval
    rename_i vs; cases vs <;> simp at heval
    cases h3 : Expr.eval σ idx <;> simp [h3] at heval
    rename_i vi; cases vi <;> simp at heval
    obtain ⟨_, rfl⟩ := heval
    simp [Value.hasType]

/-! ## Note on Progress

The theorem "a well-typed expression always evaluates to some value" does
not hold for Radix as formulated. Counter-examples:
- `e / 0` is well-typed (`uint64`) but `eval` returns `none`
- `arr[i]` may fail if `i` is out of bounds or `arr` has been freed
- `s[i]` may fail if `i ≥ s.length`

A correct formulation would require a totality judgment or strengthened
preconditions (non-zero divisors, heap liveness, bounds invariants). -/

end Radix
