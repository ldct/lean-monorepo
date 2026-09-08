import VersoSlides
import Slides

open VersoSlides

def main (args : List String) : IO UInt32 := do
  let config : Config := { center := false, margin := 0 }
  let rc ← slidesMain (config := config) (doc := %doc Slides) (args := args)
  let outputDir := config.outputDir
  -- Copy static assets into output directory
  let cssContents ← IO.FS.readFile "static/custom.css"
  IO.FS.writeFile (outputDir / "custom.css") cssContents
  let logoBytes ← IO.FS.readBinFile "static/lean-logo.png"
  IO.FS.writeBinFile (outputDir / "lean-logo.png") logoBytes
  -- Post-process HTML
  let htmlPath := outputDir / "index.html"
  let html ← IO.FS.readFile htmlPath
  -- Inject custom stylesheet at end of <head>
  let html := html.replace "</head>" "<link rel=\"stylesheet\" href=\"custom.css\">\n    </head>"
  -- Inject disableLayout into Reveal.initialize (the Stanford trick)
  let html := html.replace "Reveal.initialize({" "Reveal.initialize({\n        disableLayout: true,"
  -- Inject slide header (logo + line) into content slides (not dark slides)
  let slideHeader := "<div class=\"slide-header\"><img src=\"lean-logo.png\" alt=\"Lean\"></div>"
  -- Add header after each <section> that doesn't have data-background-color
  let html := html.replace "<section>\n" s!"<section>\n          {slideHeader}\n"
  let html := html.replace "<section data-transition=\"fade\">\n" s!"<section data-transition=\"fade\">\n          {slideHeader}\n"
  IO.FS.writeFile htmlPath html
  -- Inline hover data to avoid fetch CORS issues when opening as local files
  let docsJsonPath := outputDir / "-verso-docs.json"
  if ← docsJsonPath.pathExists then
    let docsJson ← IO.FS.readFile docsJsonPath
    -- Patch highlighting.js
    let hlJsPath := outputDir / "lib" / "highlighting.js"
    if ← hlJsPath.pathExists then
      let hlJs ← IO.FS.readFile hlJsPath
      let hlJs := hlJs.replace
        "fetch(docsJson).then((resp) => resp.json()).then((versoDocData) => {"
        s!"Promise.resolve({docsJson}).then((versoDocData) => \{"
      let hlJs := hlJs.replace
        "window.onload = () => {"
        "window.addEventListener('load', () => {"
      IO.FS.writeFile hlJsPath hlJs
    -- Patch panel.js
    let panelJsPath := outputDir / "lib" / "panel.js"
    if ← panelJsPath.pathExists then
      let panelJs ← IO.FS.readFile panelJsPath
      let panelJs := panelJs.replace
        "fetch(\"-verso-docs.json\")\n            .then(function (r) {\n                return r.ok ? r.json() : {};\n            })\n            .then(function (j) {\n                docsJson = j;\n            })\n            .catch(function () {\n                docsJson = {};\n            });"
        s!"docsJson = {docsJson};"
      IO.FS.writeFile panelJsPath panelJs
  return rc
