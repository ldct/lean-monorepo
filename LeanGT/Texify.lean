/-
texify is a tactic that displays the goal in latex form.

Adapted from explanation widget by Adam Topaz.

Contributors: Li Xuanji, Frederick Pu
-/
import Mathlib
import ProofWidgets.Component.HtmlDisplay

axiom anotherSorryAx {P} : P

macro "intentional_sorry" : tactic => `(tactic| exact anotherSorryAx)

example : ∀ (P Q : Prop), P → (P → Q) → Q := by
  intentional_sorry

open Lean Elab ProofWidgets ProofWidgets.Jsx

instance : ToString LocalDecl where
  toString (decl : LocalDecl) := decl.userName.toString

instance : ToString (Option LocalDecl) where
  toString := fun o => match o with
    | some decl => decl.userName.toString
    | none => "none"

partial def localCtxToString (ctx : LocalContext) : String := Id.run do
  let decls := ctx.decls
  let declsStr := decls.map (fun decl => s!"{decl}")
  let ret := declsStr.foldl (fun acc str => s!"{acc} {str}") ""
  return ret

instance : ToString LocalContext where
  toString := localCtxToString

/-- Displays the markdown source in `md` in a widget when the cursor is placed at `stx`. -/
def displayMarkdown (md : String) (stx : Syntax) : CoreM Unit := do
  let html : Html := <MarkdownDisplay contents={md}/>
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Lean.Expr

/-- A brute force pretty printer for expressions. -/
partial def brute_force_pp (expr : Expr) : String := match expr with
  | .bvar idx => s!"ξ_{idx}"
  | .fvar id => "fvar"
  | .mvar id => s!"?{id.name}"
  | .sort lvl => s!"Type{lvl}"
  | .const name _ => toString name
  | .app f a => s!"{brute_force_pp f}({brute_force_pp a})"
  | .lam name type body _ => s!"\\lambda {name} : {brute_force_pp type} \\mapsto {brute_force_pp body}"
  | .forallE name type body _ => s!"\\forall {name} : {brute_force_pp type}, {brute_force_pp body}"
  | .letE name type value body _ => s!"??let??"
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s!"\"{s}\""
  | .mdata _ e => s!"{brute_force_pp e}"
  | _ => s!"??unknown {expr}??"

-- For the expression a * expr, return whether we would need parentheses around expr.
partial def bind_mul (expr : Expr) : Bool := match expr with
  | .const ``HAdd.hAdd _ => true
  | .const ``HSub.hSub _ => true
  | .app f a => bind_mul f || bind_mul a
  | .lam _ _ body _ => true
  | .forallE _ _ body _ => true
  | .letE _ _ value body _ => true
  | _ => false

-- For the expression expr^a, return whether we would need parentheses around expr.
partial def bind_pow (expr : Expr) : Bool := match expr with
  | .const ``HAdd.hAdd _ => true
  | .const ``HMul.hMul _ => true
  | .const ``HPow.hPow _ => true
  | .const ``HDiv.hDiv _ => true
  | .app f a => bind_pow f || bind_pow a
  | .lam _ _ body _ => true
  | .forallE _ _ body _ => true
  | .letE _ _ value body _ => true
  | _ => false

/-- Try to pretty print an expression in latex form. -/
partial def expr_to_latex (expr : Expr) (ctx : LocalContext) : String := Id.run do

  -- skip metadata
  if expr.isMData then
    match expr with
    | .mdata _ e => return expr_to_latex e ctx
    | _ =>
      dbg_trace f!"unexpected arity for mdata"
      return brute_force_pp expr

  if expr.isFVar then
    match expr with
    | .fvar id =>
      if let some x ← ctx.find? id then
        return x.userName.toString
      else
        return "??unknown_fvar??"
    | _ => return brute_force_pp expr

  if expr.isBVar then
    -- dbg_trace f!"bvar: {expr} {ctx}"
    match expr with
    | .bvar id => return s!"ξ_{id}"
    | _ => return brute_force_pp expr

  if expr.isConstOf ``Real then return "ℝ"
  if expr.isConstOf ``Nat then return "ℕ"
  if expr.isConstOf ``Int then return "ℤ"
  if expr.isConstOf ``Rat then return "ℚ"

  if expr.isLambda then
    match expr with
    | .lam name type body _ =>
      return s!" {name} \\mapsto {expr_to_latex body ctx}"
    | _ => return brute_force_pp expr

  if let some num ← pure expr.numeral? then
    return toString num

  if (← pure (expr.isAppOfArity ``Real.sqrt 1)) then
    match (← pure (getAppArgs expr)) with
    | #[a] => return s!"\\sqrt {expr_to_latex a ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Real.sqrt"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Real.sin 1)) then
    match (← pure (getAppArgs expr)) with
    | #[a] => return s!"\\sin {expr_to_latex a ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Real.sin"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Real.cos 1)) then
    match (← pure (getAppArgs expr)) with
    | #[a] => return s!"\\cos {expr_to_latex a ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Real.cos"
      return brute_force_pp expr


  if (← pure (expr.isAppOfArity ``Real.tan 1)) then
    match (← pure (getAppArgs expr)) with
    | #[a] => return s!"\\tan {expr_to_latex a ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Real.tan"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``ZMod 1)) then
    match (← pure (getAppArgs expr)) with
    | #[a] => return s!"ℤ_\{{expr_to_latex a ctx}}"
    | _ =>
      dbg_trace f!"unexpected arity for ZMod"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HAdd.hAdd 6)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, _, _, e, f] => return s!"{expr_to_latex e ctx} + {expr_to_latex f ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for HAdd.hAdd"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HDiv.hDiv 6)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, _, _, e, f] => return s!"\\frac \{ {expr_to_latex e ctx} } \{{expr_to_latex f ctx}}"
    | _ =>
      dbg_trace f!"unexpected arity for HDiv.hDiv"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``LT.lt 4)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, c, d] => return s!"{expr_to_latex c ctx} < {expr_to_latex d ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for LT.lt"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``LE.le 4)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, c, d] => return s!"{expr_to_latex c ctx} \\leq {expr_to_latex d ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for LE.le"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HSub.hSub 6)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e, f] => return s!"{expr_to_latex e ctx} - {expr_to_latex f ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for HSub.hSub"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HMul.hMul 6)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, _, _, e, f] =>
      let e_latex ← expr_to_latex e ctx
      let f_latex ← expr_to_latex f ctx

      match (bind_mul e, bind_mul f) with
      | (true, true) => return s!"({e_latex})({f_latex})"
      | (true, false) => return s!"({e_latex}){f_latex}"
      | (false, true) => return s!"{e_latex}({f_latex})"
      | (false, false) => return s!"{e_latex} {f_latex}"
    | _ =>
      dbg_trace f!"unexpected arity for HMul.hMul"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HPow.hPow 6)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, _, _, e, f] =>
      let e_latex ← expr_to_latex e ctx
      let f_latex ← expr_to_latex f ctx

      match bind_pow e with
      | true => return s!"({e_latex})^\{{f_latex}}"
      | false => return s!"{e_latex}^\{{f_latex}}"
    | _ =>
      dbg_trace f!"unexpected arity for HPow.hPow"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Eq 3)) then
    match (← pure (getAppArgs expr)) with
    | #[_, b, c] => return s!"{expr_to_latex b ctx} = {expr_to_latex c ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Eq"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HMod.hMod 6)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e, f] => return s!"{expr_to_latex e ctx} \\bmod {expr_to_latex f ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for HMod.hMod"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Finset.Icc 5)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e] => return s!"[{expr_to_latex d ctx}, {expr_to_latex e ctx}]"
    | _ =>
      dbg_trace f!"unexpected arity for Finset.Icc"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Finset.Ico 5)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e] => return s!"[{expr_to_latex d ctx}, {expr_to_latex e ctx})"
    | _ =>
      dbg_trace f!"unexpected arity for Finset.Ico"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Finset.sum 5)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, _, d, e] =>
      -- first 3 args are types
      return s!"\\sum_\{{expr_to_latex d ctx}} \{{expr_to_latex e ctx}}"
    | _ =>
      dbg_trace f!"unexpected arity for Finset.Ico"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Finset.prod 5)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, _, d, e] =>
      -- first 3 args are types
      return s!"\\prod_\{{expr_to_latex d ctx}} \{{expr_to_latex e ctx}}"
    | _ =>
      dbg_trace f!"unexpected arity for Finset.Ico"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Finset.univ 2)) then
    match (← pure (getAppArgs expr)) with
    | #[a, _] =>
      return s!"\{{expr_to_latex a ctx}}"
    | _ =>
      dbg_trace f!"unexpected arity for Finset.univ"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Finset.range 1)) then
    match (← pure (getAppArgs expr)) with
    | #[n] =>
      return s!"<\{{expr_to_latex n ctx}}"
    | _ =>
      dbg_trace f!"unexpected arity for Finset.range"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Nat.cast 3)) then
    match (← pure (getAppArgs expr)) with
    | #[_, _, a] =>
      -- suppress casts in latex
      return s!"{expr_to_latex a ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Nat.cast"
      return brute_force_pp expr

  if expr.isApp then
    -- dbg_trace f!"app: {expr}"
    match expr with
    | .app f a =>
      let f_expr ← expr_to_latex f ctx
      if f_expr ∈ ["x", "y", "z", "a", "b", "c", "d", "e"] then
        -- heuristic: these function names are usually used as series
        -- so we should write it in subscript
        return s!"{f_expr}_\{{expr_to_latex a ctx}}"
      else
        return s!"{f_expr}({expr_to_latex a ctx})"
    | _ =>
      dbg_trace f!"unexpected arity for App"
      return brute_force_pp expr

  dbg_trace f!"unknown expression, falling back to brute force: {expr}"
  return brute_force_pp expr

end Lean.Expr

syntax (name := texifyTacticSyntax) "texify" ("at" ident*)? : tactic
namespace Lean.Expr

open Tactic in

@[tactic texifyTacticSyntax]
def elabTexify : Tactic := fun stx =>
  match stx with
  | `(tactic|texify%$tk) => do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let localCtx ← Lean.getLCtx

    -- dbg_trace f!"goal type: {goalType}"
    let texifiedExpr := expr_to_latex goalType localCtx
    -- dbg_trace f!"texifiedExpr: {texifiedExpr}"
    displayMarkdown s!"${texifiedExpr}$" tk
  | `(tactic|texify at $[$ids]* ) => do
    let localCtx ← Lean.getLCtx

    -- Extract identifiers from the comma-separated list using getElems

    -- Loop over each identifier and display its LaTeX
    ids.forM (fun h =>
      match localCtx.findFromUserName? h.getId with
      | some decl =>
        let texifiedExpr := expr_to_latex decl.type localCtx
        displayMarkdown s!"${expr_to_latex decl.type localCtx}$" stx
      | none => throwError "Unknown hypothesis {h.getId}")
  | _ => throwUnsupportedSyntax

end Lean.Expr

-- function calls
example
  (f : ℝ → ℝ)
: 0 < f 0 := by
  texify
  intentional_sorry

--  metadata is skipped
example (x y : ℝ) : 0 < x^(x + y) := by
  have triv : 1 = 1 := by decide
  texify
  intentional_sorry

-- Why is this failing?
example (x y : ℝ) : 0 < x^(x + y) := by
  have triv: x = y := by
    texify -- ok
    intentional_sorry

  have triv'' (a : ℝ) : a = a := by
    texify -- fails
    intentional_sorry

  intentional_sorry


def f (x : ZMod 5) : ℕ := 2

example (i : ZMod 102) : i = 3 := by
  have (x y : ℝ) : x = y := by
    texify
    intentional_sorry

  texify
  intentional_sorry

example (x : ZMod 5) : x = x := by
  texify at x
  sorry

example (a : ℕ) (x : ZMod a) : x = x := by
  texify at x
  sorry

example : ∑ j, f j = 10 := by
  texify
  decide

-- Test cases : x*(x ∘ y)

example (x y : ℝ) : 0 < x^(x + y) := by
  texify
  intentional_sorry

example (x y : ℝ) : 0 < x^(x * y) := by
  texify
  intentional_sorry

example (x y : ℝ) : 0 < x^(x / y) := by
  texify
  intentional_sorry

example (x y : ℝ) : 0 < x^(x^y) := by
  texify
  intentional_sorry

example (x y : ℝ) : 0 < (x^x)^y := by
  texify
  intentional_sorry

example (x y : ℝ) : 0 < (x+x)^y := by
  texify
  intentional_sorry

example (x y : ℝ) : 0 < (x+x)^(x+y) := by
  texify
  intentional_sorry

example (x y : ℝ): 0 < (x*(x+y)) := by
  texify
  intentional_sorry

example (x y : ℝ): 0 < (x*(x-y)) := by
  texify
  intentional_sorry

example (x y : ℝ): 0 < (x*(x^y)) := by
  texify
  intentional_sorry

example (x y : ℝ): 0 < (x*(x*y)) := by
  texify
  intentional_sorry

example (x y : ℝ): 0 < x^2 * y^2 := by
  texify
  intentional_sorry

example (x y : ℝ): 0 < (x*y)^2 := by
  texify
  intentional_sorry

example (x y : ℝ): 0 < (x+y)^2 := by
  texify
  intentional_sorry

-- This one is tough to format nicely...
theorem multi (a b c d : ℝ)
  : 0 ≤ (a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d) := by
  texify
  intentional_sorry

example : 3 % 2 = 1 := by
  texify
  norm_num

lemma lemma0 (n : ℕ) : (∑ x ∈ Finset.Icc 1 (4 * n + 2), (x:ℤ) % 2) % 2 = 1 := by
  texify
  sorry
