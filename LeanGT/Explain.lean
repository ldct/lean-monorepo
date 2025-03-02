/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib
import ProofWidgets.Component.HtmlDisplay

/-!

# Explanation Widgets

This file defines some simple widgets wrapped in a tactic, term and command elaborator
that display nicely rendered markdown in the infoview.

Example tactic usage:
```
example : True := by
  explain "This is the first step."
  explain "This is the last step." in
    exact trivial
```
Placing the cursor on each line results will render the explanation in the infoview.

Example term usage:
```
example : Nat := explain "This is zero" in
  0
```
Placing the cursor on the term will render the explanation in the infoview.


Example command usage:
```
#explain "This is an explanation."
```
This will render the provided text in the infoview.


# Implementation

This code uses `MarkdownDisplay` from `ProofWidgets`, and thus supports
markdown and latex via mathjax.

-/

open Lean Elab ProofWidgets ProofWidgets.Jsx

/-- Displays the markdown source in `md` in a widget when the cursor is placed at `stx`. -/
def displayMarkdown (md : String) (stx : Syntax) : CoreM Unit := do
  let html : Html := <MarkdownDisplay contents={md}/>
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

/-- Syntax for the `explain` tactic elaborator. -/
syntax (name := explainTacStx) "explain" str ("in" ppIndent(tactic))? : tactic


set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Lean.Expr

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

partial def expr_to_latex (expr : Expr) (ctx : LocalContext) : String := Id.run do

  if expr.isFVar then
    match expr with
    | .fvar id =>
      let x ← ctx.get! id
      return x.userName.toString
    | _ => return brute_force_pp expr

  if let some num ← pure expr.numeral? then
    return toString num

  if (← pure (expr.isAppOfArity ``HAdd.hAdd 6)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e, f] => return s!"{expr_to_latex e ctx} + {expr_to_latex f ctx}"
    | _ => return brute_force_pp expr

  if (← pure (expr.isAppOfArity ``HDiv.hDiv 6)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c, d, e, f] => return s!"\\frac \{ {expr_to_latex e ctx} } \{{expr_to_latex f ctx}}"
    | _ => return brute_force_pp expr


  if (← pure (expr.isAppOfArity ``Eq 3)) then
    match (← pure (getAppArgs expr)) with
    | #[a, b, c] => return s!"{expr_to_latex b ctx} = {expr_to_latex c ctx}"
    | _ => return brute_force_pp expr

  return brute_force_pp expr

open Tactic in
/-- A tactic that adds an explanation widget in markdown form. -/
@[tactic explainTacStx]
def elabExplainTac : Tactic := fun stx =>
  match stx with
  | `(tactic|explain%$tk $s:str) => do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let localCtx ← Lean.getLCtx

    -- dbg_trace f!"goal type: {goalType}"
    displayMarkdown s!"${(expr_to_latex goalType localCtx)}$" tk
  | _ => throwUnsupportedSyntax


example (x y :ℝ): x = x / y := by
  explain "This is the first step. $x+y$"
  sorry
