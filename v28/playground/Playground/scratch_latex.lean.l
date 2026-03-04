import ProofWidgets
import Lean

open Lean ProofWidgets ProofWidgets.Jsx

open Elab Command in
elab "#explain" t:term : command => liftTermElabM do
  let tt ← Term.elabTerm t <| some (.const `String [])
  let src ← unsafe Meta.evalExpr String (.const `String []) tt
  let html : Html := <MarkdownDisplay contents = {src} />
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    t

#explain "$x+1 ∑$ bar"
