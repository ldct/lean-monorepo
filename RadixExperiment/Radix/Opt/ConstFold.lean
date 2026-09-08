/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Stmt

/-! # Constant Folding

Fold constant expressions: `3 + 4 → 7`, `true && e → e`, etc.
Includes algebraic identity simplifications (e.g. `e + 0 → e`) guarded
by structural type inference, with a correctness proof that the
optimization preserves semantics.

## Identity vs. absorb rules

Identity simplifications like `e + 0 → e` are sound with a type guard: when
we know `e` produces a `uint64` (if it succeeds at all), then
`BinOp.eval .add v (.uint64 0) = some v`.

Absorb simplifications like `e * 0 → 0` are NOT sound without guaranteeing
that `e.eval σ` succeeds: if `e.eval σ = none`, the original expression
produces `none` but the simplified one produces `some (.uint64 0)`.  Since
`Expr.inferTag` cannot guarantee evaluation success (only the result type
when it does succeed), absorb rules are omitted.  They require a full type
system with totality guarantees to be sound.
-/

namespace Radix

/-! ## Value type tags and structural type inference -/

/-- Type tag of a runtime value. -/
inductive ValTag where
  | uint64 | bool | str | unit | addr
  deriving DecidableEq, Repr

/-- Extract the type tag from a value. -/
@[simp] def Value.tag : Value → ValTag
  | .uint64 _ => .uint64
  | .bool _   => .bool
  | .str _    => .str
  | .unit     => .unit
  | .addr _   => .addr

/-- What tag does a `BinOp` produce when fed operands of the given tags? -/
@[simp] def BinOp.resultTag : BinOp → ValTag → ValTag → Option ValTag
  | .add, .uint64, .uint64 | .sub, .uint64, .uint64
  | .mul, .uint64, .uint64 | .div, .uint64, .uint64
  | .mod, .uint64, .uint64 => some .uint64
  | .eq, _, _ | .ne, _, _ => some .bool
  | .lt, .uint64, .uint64 | .le, .uint64, .uint64
  | .gt, .uint64, .uint64 | .ge, .uint64, .uint64 => some .bool
  | .and, .bool, .bool | .or, .bool, .bool => some .bool
  | .strAppend, .str, .str => some .str
  | _, _, _ => none

/-- What tag does a `UnaryOp` produce when fed an operand of the given tag? -/
@[simp] def UnaryOp.resultTag : UnaryOp → ValTag → Option ValTag
  | .not, .bool   => some .bool
  | .neg, .uint64 => some .uint64
  | _, _          => none

/-- Conservative structural type inference for constant folding.
Returns `some tag` only when we can statically guarantee that every
successful evaluation produces a value with that tag. Returns `none`
for variables, array indexing, etc., where the result depends on
runtime state. This is weaker than full type checking but does not
require a type environment -- it works purely from the expression
structure.

Soundness: `Expr.inferTag_sound` proves that if `inferTag` returns
`some tag` and evaluation succeeds, the result has that tag. -/
def Expr.inferTag : Expr → Option ValTag
  | .lit v        => some v.tag
  | .var _        => none
  | .binop op l r => do
    let tl ← l.inferTag
    let tr ← r.inferTag
    op.resultTag tl tr
  | .unop op e    => do
    let t ← e.inferTag
    op.resultTag t
  | .arrGet ..    => none
  | .arrLen _     => some .uint64
  | .strLen _     => some .uint64
  | .strGet ..    => some .str

/-! ### Soundness of tag inference -/

private theorem BinOp.resultTag_sound (op : BinOp) (v₁ v₂ r : Value) (tag : ValTag)
    (htag : op.resultTag v₁.tag v₂.tag = some tag) (heval : op.eval v₁ v₂ = some r) :
    r.tag = tag := by
  cases op <;> cases v₁ <;> cases v₂ <;>
    simp [BinOp.eval, BinOp.resultTag, Value.tag] at htag heval ⊢ <;>
    (try subst_vars; try rfl) <;>
    (try (obtain ⟨_, h⟩ := heval; subst h; rfl))

private theorem UnaryOp.resultTag_sound (op : UnaryOp) (v r : Value) (tag : ValTag)
    (htag : op.resultTag v.tag = some tag) (heval : op.eval v = some r) :
    r.tag = tag := by
  cases op <;> cases v <;> simp [UnaryOp.eval, UnaryOp.resultTag, Value.tag] at htag heval ⊢ <;>
    subst_vars <;> rfl

theorem Expr.inferTag_sound : ∀ (e : Expr) (σ : PState) (tag : ValTag) (v : Value),
    e.inferTag = some tag → e.eval σ = some v → v.tag = tag
  | .lit _, _, _, v, htag, heval => by
    simp [inferTag, Expr.eval] at htag heval; rw [← heval]; exact htag
  | .var _, _, _, _, htag, _ => by simp [inferTag] at htag
  | .binop op l r, σ, tag, v, htag, heval => by
    unfold inferTag at htag
    revert htag
    cases htl : l.inferTag with
    | none => simp
    | some tl =>
      cases htr : r.inferTag with
      | none => simp
      | some tr =>
        simp; intro hrt
        simp only [Expr.eval] at heval
        revert heval
        cases hl : l.eval σ with
        | none => simp
        | some vl =>
          cases hr : r.eval σ with
          | none => simp
          | some vr =>
            simp; intro hev
            exact BinOp.resultTag_sound op vl vr v tag
              (by rw [inferTag_sound l σ tl vl htl hl,
                      inferTag_sound r σ tr vr htr hr]; exact hrt) hev
  | .unop op e, σ, tag, v, htag, heval => by
    unfold inferTag at htag
    revert htag
    cases hte : e.inferTag with
    | none => simp
    | some te =>
      simp; intro hrt
      simp only [Expr.eval] at heval
      revert heval
      cases he : e.eval σ with
      | none => simp
      | some ve =>
        simp; intro hev
        exact UnaryOp.resultTag_sound op ve v tag
          (by rw [inferTag_sound e σ te ve hte he]; exact hrt) hev
  | .arrGet .., _, _, _, htag, _ => by simp [inferTag] at htag
  | .arrLen arr, σ, _, v, htag, heval => by
    simp [inferTag] at htag; subst htag
    unfold Expr.eval at heval
    -- Split on arr.eval σ
    cases h1 : arr.eval σ with
    | none => simp [h1] at heval
    | some va =>
      simp [h1] at heval
      cases va with
      | addr a =>
        simp at heval
        cases h2 : σ.heap.arraySize a with
        | none => simp [h2] at heval
        | some sz => simp [h2] at heval; subst heval; rfl
      | uint64 _ | bool _ | unit | str _ => simp at heval
  | .strLen s, σ, _, v, htag, heval => by
    simp [inferTag] at htag; subst htag
    unfold Expr.eval at heval
    cases h1 : s.eval σ with
    | none => simp [h1] at heval
    | some vs =>
      simp [h1] at heval
      cases vs with
      | str sv => simp at heval; subst heval; rfl
      | uint64 _ | bool _ | unit | addr _ => simp at heval
  | .strGet s idx, σ, _, v, htag, heval => by
    simp [inferTag] at htag; subst htag
    unfold Expr.eval at heval
    cases h1 : s.eval σ with
    | none => simp [h1] at heval
    | some vs =>
      simp [h1] at heval
      cases vs with
      | str sv =>
        simp at heval
        cases h2 : idx.eval σ with
        | none => simp [h2] at heval
        | some vi =>
          simp [h2] at heval
          cases vi with
          | uint64 i =>
            simp at heval
            obtain ⟨_, heq⟩ := heval; subst heq; rfl
          | bool _ | unit | str _ | addr _ => simp at heval
      | uint64 _ | bool _ | unit | addr _ => simp at heval

/-! ### Corollaries for specific tags -/

private theorem eval_uint64_of_inferTag (e : Expr) (σ : PState) (v : Value)
    (htag : e.inferTag = some .uint64) (heval : e.eval σ = some v) :
    ∃ n : UInt64, v = .uint64 n := by
  have := Expr.inferTag_sound e σ .uint64 v htag heval
  cases v <;> simp_all [Value.tag]

private theorem eval_bool_of_inferTag (e : Expr) (σ : PState) (v : Value)
    (htag : e.inferTag = some .bool) (heval : e.eval σ = some v) :
    ∃ b : Bool, v = .bool b := by
  have := Expr.inferTag_sound e σ .bool v htag heval
  cases v <;> simp_all [Value.tag]

private theorem eval_str_of_inferTag (e : Expr) (σ : PState) (v : Value)
    (htag : e.inferTag = some .str) (heval : e.eval σ = some v) :
    ∃ s : String, v = .str s := by
  have := Expr.inferTag_sound e σ .str v htag heval
  cases v <;> simp_all [Value.tag]

/-! ## BinOp and UnaryOp simplification -/

/-- Simplify a binary operation.

**Constant folding**: When both operands are literals, evaluate at compile time.

**Identity simplifications**: When one operand is an identity element (e.g. `0`
for `+`, `1` for `*`, `true` for `&&`, `false` for `||`, `""` for `++`),
and `Expr.inferTag` confirms the other operand has the correct type tag,
simplify to the other operand.

Note: absorb rules (`e * 0 → 0`, `false && e → false`, `true || e → true`)
are intentionally omitted because they are unsound when `e.eval σ = none`. -/
def BinOp.simplify : BinOp → Expr → Expr → Expr
  -- Pure constant folding (both literals)
  | .add, .lit (.uint64 a), .lit (.uint64 b) => .lit (.uint64 (a + b))
  | .sub, .lit (.uint64 a), .lit (.uint64 b) => .lit (.uint64 (a - b))
  | .mul, .lit (.uint64 a), .lit (.uint64 b) => .lit (.uint64 (a * b))
  | .eq,  .lit a,           .lit b           => .lit (.bool (a == b))
  | .ne,  .lit a,           .lit b           => .lit (.bool (a != b))
  | .and, .lit (.bool a),   .lit (.bool b)   => .lit (.bool (a && b))
  | .or,  .lit (.bool a),   .lit (.bool b)   => .lit (.bool (a || b))
  | .strAppend, .lit (.str a), .lit (.str b) => .lit (.str (a ++ b))
  -- Additive identity: e + 0 = e, 0 + e = e
  | .add, e, .lit (.uint64 0) =>
    if e.inferTag == some .uint64 then e else .binop .add e (.lit (.uint64 0))
  | .add, .lit (.uint64 0), e =>
    if e.inferTag == some .uint64 then e else .binop .add (.lit (.uint64 0)) e
  -- Subtractive identity: e - 0 = e
  | .sub, e, .lit (.uint64 0) =>
    if e.inferTag == some .uint64 then e else .binop .sub e (.lit (.uint64 0))
  -- Multiplicative identity: e * 1 = e, 1 * e = e
  | .mul, e, .lit (.uint64 1) =>
    if e.inferTag == some .uint64 then e else .binop .mul e (.lit (.uint64 1))
  | .mul, .lit (.uint64 1), e =>
    if e.inferTag == some .uint64 then e else .binop .mul (.lit (.uint64 1)) e
  -- Boolean AND identity: true && e = e, e && true = e
  | .and, .lit (.bool true), e =>
    if e.inferTag == some .bool then e else .binop .and (.lit (.bool true)) e
  | .and, e, .lit (.bool true) =>
    if e.inferTag == some .bool then e else .binop .and e (.lit (.bool true))
  -- Boolean OR identity: false || e = e, e || false = e
  | .or, .lit (.bool false), e =>
    if e.inferTag == some .bool then e else .binop .or (.lit (.bool false)) e
  | .or, e, .lit (.bool false) =>
    if e.inferTag == some .bool then e else .binop .or e (.lit (.bool false))
  -- String identity: e ++ "" = e, "" ++ e = e
  | .strAppend, e, .lit (.str "") =>
    if e.inferTag == some .str then e else .binop .strAppend e (.lit (.str ""))
  | .strAppend, .lit (.str ""), e =>
    if e.inferTag == some .str then e else .binop .strAppend (.lit (.str "")) e
  -- Fallthrough
  | op, a, b => .binop op a b

def UnaryOp.simplify : UnaryOp → Expr → Expr
  | .not, .lit (.bool b) => .lit (.bool !b)
  | op, e => .unop op e

/-- Recursively apply constant folding to all subexpressions. -/
def Expr.constFold : Expr → Expr
  | .lit v => .lit v
  | .var x => .var x
  | .binop op l r => BinOp.simplify op l.constFold r.constFold
  | .unop op e => UnaryOp.simplify op e.constFold
  | .arrGet arr idx => .arrGet arr.constFold idx.constFold
  | .arrLen arr => .arrLen arr.constFold
  | .strLen s => .strLen s.constFold
  | .strGet s idx => .strGet s.constFold idx.constFold

def Expr.constFoldList (es : List Expr) : List Expr :=
  es.map Expr.constFold

mutual
def Stmt.constFold : Stmt → Stmt
  | .skip => .skip
  | .assign x e => .assign x (Expr.constFold e)
  | .seq s₁ s₂ => .seq s₁.constFold s₂.constFold
  | .ite c t f =>
    match Expr.constFold c with
    | .lit (.bool true) => t.constFold
    | .lit (.bool false) => f.constFold
    | c' => .ite c' t.constFold f.constFold
  | .while c b =>
    match Expr.constFold c with
    | .lit (.bool false) => .skip
    | c' => .while c' b.constFold
  | .decl x ty e => .decl x ty (Expr.constFold e)
  | .alloc x ty sz => .alloc x ty (Expr.constFold sz)
  | .free e => .free (Expr.constFold e)
  | .arrSet arr idx val =>
    .arrSet (Expr.constFold arr) (Expr.constFold idx) (Expr.constFold val)
  | .ret e => .ret (Expr.constFold e)
  | .block stmts => .block (Stmt.constFoldList stmts)
  | .callStmt f args => .callStmt f (Expr.constFoldList args)
  | .scope ps as body => .scope ps (Expr.constFoldList as) body.constFold

def Stmt.constFoldList : List Stmt → List Stmt
  | [] => []
  | s :: ss => s.constFold :: Stmt.constFoldList ss
end

/-! ## Correctness proofs -/

-- Identity lemmas for specific operations
private theorem add_zero_right (e : Expr) (σ : PState) (htag : e.inferTag = some .uint64) :
    e.eval σ = (e.eval σ).bind (fun vl => BinOp.eval .add vl (.uint64 0)) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨n, rfl⟩ := eval_uint64_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem add_zero_left (e : Expr) (σ : PState) (htag : e.inferTag = some .uint64) :
    e.eval σ = (e.eval σ).bind (fun vr => BinOp.eval .add (.uint64 0) vr) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨n, rfl⟩ := eval_uint64_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem sub_zero_right (e : Expr) (σ : PState) (htag : e.inferTag = some .uint64) :
    e.eval σ = (e.eval σ).bind (fun vl => BinOp.eval .sub vl (.uint64 0)) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨n, rfl⟩ := eval_uint64_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem mul_one_right (e : Expr) (σ : PState) (htag : e.inferTag = some .uint64) :
    e.eval σ = (e.eval σ).bind (fun vl => BinOp.eval .mul vl (.uint64 1)) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨n, rfl⟩ := eval_uint64_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem mul_one_left (e : Expr) (σ : PState) (htag : e.inferTag = some .uint64) :
    e.eval σ = (e.eval σ).bind (fun vr => BinOp.eval .mul (.uint64 1) vr) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨n, rfl⟩ := eval_uint64_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem and_true_left (e : Expr) (σ : PState) (htag : e.inferTag = some .bool) :
    e.eval σ = (e.eval σ).bind (fun vr => BinOp.eval .and (.bool true) vr) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨b, rfl⟩ := eval_bool_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem and_true_right (e : Expr) (σ : PState) (htag : e.inferTag = some .bool) :
    e.eval σ = (e.eval σ).bind (fun vl => BinOp.eval .and vl (.bool true)) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨b, rfl⟩ := eval_bool_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem or_false_left (e : Expr) (σ : PState) (htag : e.inferTag = some .bool) :
    e.eval σ = (e.eval σ).bind (fun vr => BinOp.eval .or (.bool false) vr) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨b, rfl⟩ := eval_bool_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem or_false_right (e : Expr) (σ : PState) (htag : e.inferTag = some .bool) :
    e.eval σ = (e.eval σ).bind (fun vl => BinOp.eval .or vl (.bool false)) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨b, rfl⟩ := eval_bool_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem strAppend_empty_right (e : Expr) (σ : PState) (htag : e.inferTag = some .str) :
    e.eval σ = (e.eval σ).bind (fun vl => BinOp.eval .strAppend vl (.str "")) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨s, rfl⟩ := eval_str_of_inferTag e σ v htag hev; simp [BinOp.eval]

private theorem strAppend_empty_left (e : Expr) (σ : PState) (htag : e.inferTag = some .str) :
    e.eval σ = (e.eval σ).bind (fun vr => BinOp.eval .strAppend (.str "") vr) := by
  cases hev : e.eval σ with | none => simp | some v =>
  obtain ⟨s, rfl⟩ := eval_str_of_inferTag e σ v htag hev; simp [BinOp.eval]

-- Helper: BinOp.simplify preserves evaluation semantics
@[simp] theorem BinOp.simplify_correct (op : BinOp) (e₁ e₂ : Expr) (σ : PState) :
    (BinOp.simplify op e₁ e₂).eval σ = (Expr.binop op e₁ e₂).eval σ := by
  simp only [Expr.eval]
  unfold BinOp.simplify
  split
  -- Each branch: either a constant folding case (closed by simp), a fallthrough
  -- (closed by rfl/simp), or an identity case with if-then-else.
  <;> first | (simp_all [Expr.eval, BinOp.eval]; done) | skip
  -- Remaining: identity cases with `if inferTag ... then ... else ...`
  all_goals (
    split
    · -- Guard true: use identity lemma.
      next htag =>
        simp only [beq_iff_eq] at htag
        -- Normalize do-notation (Bind.bind) to Option.bind,
        -- then reduce `(some x).bind f` to `f x`.
        -- Do NOT unfold BinOp.eval so the goal matches identity lemma form.
        simp only [Expr.eval, bind, Option.bind_some]
        first
        | exact add_zero_right _ σ htag
        | exact add_zero_left  _ σ htag
        | exact sub_zero_right _ σ htag
        | exact mul_one_right  _ σ htag
        | exact mul_one_left   _ σ htag
        | exact and_true_left  _ σ htag
        | exact and_true_right _ σ htag
        | exact or_false_left  _ σ htag
        | exact or_false_right _ σ htag
        | exact strAppend_empty_right _ σ htag
        | exact strAppend_empty_left  _ σ htag
    · -- Guard false: keep the binop — result is the same expression
      simp only [Expr.eval]
  )

-- Helper: UnaryOp.simplify preserves evaluation semantics
@[simp] theorem UnaryOp.simplify_correct (op : UnaryOp) (e : Expr) (σ : PState) :
    (UnaryOp.simplify op e).eval σ = (Expr.unop op e).eval σ := by
  simp [Expr.eval]; unfold UnaryOp.simplify
  split <;> simp_all [Expr.eval, UnaryOp.eval]

/-- Constant folding preserves expression evaluation for all states. -/
theorem Expr.eval_constFold (e : Expr) (σ : PState) :
    e.constFold.eval σ = e.eval σ := by
  induction e with
  | lit v => simp [Expr.constFold, Expr.eval]
  | var x => simp [Expr.constFold, Expr.eval]
  | binop op l r ihl ihr =>
    simp only [Expr.constFold, BinOp.simplify_correct, Expr.eval, ihl, ihr]
  | unop op e ih =>
    simp only [Expr.constFold, UnaryOp.simplify_correct, Expr.eval, ih]
  | arrGet arr idx iha ihi => simp only [Expr.constFold, Expr.eval, iha, ihi]
  | arrLen arr ih => simp only [Expr.constFold, Expr.eval, ih]
  | strLen s ih => simp only [Expr.constFold, Expr.eval, ih]
  | strGet s idx ihs ihi => simp only [Expr.constFold, Expr.eval, ihs, ihi]

-- Helper: constFold distributes over foldl of seq
private theorem constFold_foldl_seq (acc : Stmt) (stmts : List Stmt) :
    (stmts.foldl (init := acc) (· ;; ·)).constFold =
    (Stmt.constFoldList stmts).foldl (init := acc.constFold) (· ;; ·) := by
  induction stmts generalizing acc with
  | nil => simp [Stmt.constFoldList, List.foldl]
  | cons s ss ih =>
    simp only [List.foldl, Stmt.constFoldList]
    rw [ih]; simp [Stmt.constFold]

private theorem constFold_foldl_skip (stmts : List Stmt) :
    (stmts.foldl (init := Stmt.skip) (· ;; ·)).constFold =
    (Stmt.constFoldList stmts).foldl (init := Stmt.skip) (· ;; ·) := by
  have := constFold_foldl_seq Stmt.skip stmts
  simp [Stmt.constFold] at this; exact this

-- Helper: constFoldList preserves mapM eval
private theorem constFoldList_mapM_eval (args : List Expr) (σ : PState) :
    (Expr.constFoldList args).mapM (Expr.eval σ) = args.mapM (Expr.eval σ) := by
  induction args with
  | nil => simp [Expr.constFoldList]
  | cons e es ih =>
    unfold Expr.constFoldList
    simp only [List.map_cons, List.mapM_cons, Expr.eval_constFold]
    unfold Expr.constFoldList at ih
    rw [ih]

/-- Constant folding preserves big-step semantics: if `s` produces result `r`,
then `s.constFold` also produces `r`. The proof proceeds by induction on the
derivation, using `Expr.eval_constFold` to rewrite expression evaluations. -/
theorem Stmt.constFold_correct (h : BigStep σ s r) : BigStep σ s.constFold r := by
  induction h with
  | skip => exact BigStep.skip
  | assign he hs =>
    simp only [Stmt.constFold]
    exact BigStep.assign (by simp [Expr.eval_constFold, he]) hs
  | decl he hs =>
    simp only [Stmt.constFold]
    exact BigStep.decl (by simp [Expr.eval_constFold, he]) hs
  | seqNormal _ _ ih₁ ih₂ =>
    simp only [Stmt.constFold]; exact BigStep.seqNormal ih₁ ih₂
  | seqReturn _ ih₁ =>
    simp only [Stmt.constFold]; exact BigStep.seqReturn ih₁
  | ifTrue hc _ ih =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · exact ih
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact BigStep.ifTrue hc' ih
  | ifFalse hc _ ih =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact ih
    · exact BigStep.ifFalse hc' ih
  | whileTrue hc _ _ ihb ihw =>
    simp only [Stmt.constFold] at ihw ⊢
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split at *
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact BigStep.whileTrue hc' ihb ihw
  | whileReturn hc _ ihb =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact BigStep.whileReturn hc' ihb
  | whileFalse hc =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · exact BigStep.skip
    · exact BigStep.whileFalse hc'
  | alloc hsz ha hs =>
    simp only [Stmt.constFold]
    exact BigStep.alloc (by simp [Expr.eval_constFold, hsz]) ha hs
  | free he hf =>
    simp only [Stmt.constFold]
    exact BigStep.free (by simp [Expr.eval_constFold, he]) hf
  | arrSet harr hidx hval hw =>
    simp only [Stmt.constFold]
    exact BigStep.arrSet
      (by simp [Expr.eval_constFold, harr])
      (by simp [Expr.eval_constFold, hidx])
      (by simp [Expr.eval_constFold, hval]) hw
  | ret he =>
    simp only [Stmt.constFold]
    exact BigStep.ret (by simp [Expr.eval_constFold, he])
  | block _ ih =>
    simp only [Stmt.constFold]
    exact BigStep.block (by rw [← constFold_foldl_skip]; exact ih)
  | callStmt hlook hargs hparams hframe hbody hpop _ =>
    simp only [Stmt.constFold]
    exact BigStep.callStmt hlook
      (by rw [constFoldList_mapM_eval]; exact hargs)
      hparams hframe hbody hpop
  | scope hargs hlen hframe hbody hpop ih_body =>
    simp only [Stmt.constFold]
    exact BigStep.scope
      (by rw [constFoldList_mapM_eval]; exact hargs)
      hlen hframe ih_body hpop

end Radix
