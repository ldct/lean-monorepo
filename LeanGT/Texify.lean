/-
texify is a tactic that displays the goal in latex form.

Adapted from explanation widget by Adam Topaz.
-/
import Mathlib
import ProofWidgets.Component.HtmlDisplay

open Lean Elab ProofWidgets ProofWidgets.Jsx

/-- Displays the markdown source in `md` in a widget when the cursor is placed at `stx`. -/
def displayMarkdown (md : String) (stx : Syntax) : CoreM Unit := do
  let html : Html := <MarkdownDisplay contents={md}/>
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

syntax (name := texifyTacticSyntax) "texify" : tactic


set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Lean.Expr

/-- A brute force pretty printer for expressions. -/
partial def brute_force_pp (expr : Expr) : String := match expr with
  | .bvar idx => s!"x_{idx}"
  | .fvar id => "fvar"
  | .mvar id => s!"?{id.name}"
  | .sort lvl => s!"Type{lvl}"
  | .const name _ => toString name
  | .app f a => s!"{brute_force_pp f}({brute_force_pp a})"
  | .lam name type body _ => s!"\\lambda {name} : {brute_force_pp type} \\mapsto {brute_force_pp body}"
  | .forallE name type body _ => s!"\\forall {name} : {brute_force_pp type}, {brute_force_pp body}"
  | .letE name type value body _ => s!"???"
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s!"\"{s}\""
  | _ => "???"

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
  if expr.isFVar then
    match expr with
    | .fvar id =>
      let x ← ctx.get! id
      return x.userName.toString
    | _ => return brute_force_pp expr

  if let some num ← pure expr.numeral? then
    return toString num

  if (← pure (expr.isAppOfArity ``Real.sqrt 1)) then
    match (← pure (getAppArgs expr)) with
    | #[a] => return s!"\\sqrt {expr_to_latex a ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Real.sqrt"
      return brute_force_pp expr


  if (← pure (expr.isAppOfArity ``HAdd.hAdd 6)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e, f] => return s!"{expr_to_latex e ctx} + {expr_to_latex f ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for HAdd.hAdd"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HDiv.hDiv 6)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e, f] => return s!"\\frac \{ {expr_to_latex e ctx} } \{{expr_to_latex f ctx}}"
    | _ =>
      dbg_trace f!"unexpected arity for HDiv.hDiv"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``LT.lt 4)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d] => return s!"{expr_to_latex c ctx} < {expr_to_latex d ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for LT.lt"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``LE.le 4)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d] => return s!"{expr_to_latex c ctx} \\leq {expr_to_latex d ctx}"
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
    | #[a, b, c, d, e, f] =>
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
    | #[a, b, c, d, e, f] =>
      let e_latex ← expr_to_latex e ctx
      let f_latex ← expr_to_latex f ctx

      match bind_pow e with
      | true => return s!"({e_latex})^{f_latex}"
      | false => return s!"{e_latex}^{f_latex}"
    | _ =>
      dbg_trace f!"unexpected arity for HPow.hPow"
      return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``Eq 3)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c] => return s!"{expr_to_latex b ctx} = {expr_to_latex c ctx}"
    | _ =>
      dbg_trace f!"unexpected arity for Eq"
      return brute_force_pp expr

  return brute_force_pp expr

open Tactic in

/-- A tactic that adds an explanation widget in markdown form. -/
@[tactic texifyTacticSyntax]
def elabExplainTac : Tactic := fun stx =>
  match stx with
  | `(tactic|texify%$tk) => do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let localCtx ← Lean.getLCtx

    -- dbg_trace f!"goal type: {goalType}"
    -- displayMarkdown s!"{(expr_to_latex goalType localCtx)}" tk
    displayMarkdown s!"${(expr_to_latex goalType localCtx)}$" tk
  | _ => throwUnsupportedSyntax


-- Test cases : x*(x ∘ y)

example (x y : ℝ): 0 < (x*(x+y)) := by
  texify
  sorry

example (x y : ℝ): 0 < (x*(x-y)) := by
  texify
  sorry

example (x y : ℝ): 0 < (x*(x^y)) := by
  texify
  sorry

example (x y : ℝ): 0 < (x*(x*y)) := by
  texify
  sorry

example (x y : ℝ): 0 < x^2 * y^2 := by
  texify
  sorry

example (x y : ℝ): 0 < (x*y)^2 := by
  texify
  sorry

example (x y : ℝ): 0 < (x+y)^2 := by
  texify
  sorry

theorem motzkin (x y : ℝ) : 0 ≤ x^4 * y^2 + x^2 * y^4  - 3 * x^2 * y^2 + 1 := by
  texify
  sorry

theorem nesbitt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : (3:ℝ) / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) := by
  texify
  sorry

theorem nesbitt' (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
  : 2 ≤ a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) := by
  texify
  sorry

theorem example_111 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : a*b + b*c + c*a ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  texify
  sorry

theorem imosl1998SL (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x*y*z = 1)
  : (3:ℝ) / 4 ≤ x^3 / ((1 + y) * (1 + z)) + y^3 / ((1 + z) * (1 + x)) + z^3 / ((1 + x) * (1 + y)):= by
  texify
  sorry
