#!/usr/bin/env python3
"""Assemble site/real_instances.html from the NormedField template.

Takes site/normedfield_hierarchy.html (never modified) and swaps:
  * <title>, header <h1> + subtitle
  * the inlined graphviz SVG        -> site/real_hierarchy.svg
  * const CLASS_DATA = {...}        -> site/real_tooltip_data.json (array -> dict by name)
  * let EXTRA_DATA = {...}          -> site/real_extras.json
  * the footer (adds the curation rule + frontier note)
The interactive JS is kept verbatim: the SVG honors the same attribute
contract (g.node[data-class-name], g.edge > title "S->T").

Rerunnable; also refreshes the EXTRA_DATA line in an existing
site/real_instances.html output (same marker as inject_extras.py).
Run: python3 scripts/build_real_page.py
"""
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
SITE = HERE.parent / 'site'

template = (SITE / 'normedfield_hierarchy.html').read_text()
svg = (SITE / 'real_hierarchy.svg').read_text()
tooltip = json.load(open(SITE / 'real_tooltip_data.json'))
extras = json.load(open(SITE / 'real_extras.json'))
inp = json.load(open(HERE / 'real_input.json'))
meta = inp['meta']

def jsblob(data):
    s = json.dumps(data, ensure_ascii=False, separators=(',', ':'))
    return s.replace('</', '<\\/')  # never close the <script> tag

html = template

# ---- title & header ----
html = html.replace(
    '<title>NormedField structure hierarchy — Mathlib (July 2026)</title>',
    '<title>Type classes of ℝ — Mathlib (July 2026)</title>')
html = html.replace(
    '<h1>Structure hierarchy underlying <code>NormedField</code></h1>',
    '<h1>Type classes that <code>ℝ</code> satisfies in Mathlib</h1>')
n_solid = sum(1 for e in inp['edges'] if e['kind'] == 'solid')
n_dashed = len(inp['edges']) - n_solid
sub_old = re.search(r'<span class="sub">mathlib4 master.*?</span>', html).group(0)
sub_new = (f'<span class="sub">mathlib4 master, July 2026 · {len(inp["nodes"])} of '
           f'{meta["satisfiedTotal"]} satisfied classes · {len(inp["edges"])} drawn edges '
           f'({n_solid} extends, {n_dashed} derived instances; transitively reduced, '
           'solid-preferring) · amber outline = maximal · layout grouped by subject area</span>')
html = html.replace(sub_old, sub_new)

# ---- SVG swap ----
html, n = re.subn(r'(<div id="canvas">\n).*?</svg>\n',
                  lambda m: m.group(1) + svg, html, count=1, flags=re.S)
assert n == 1, 'canvas SVG block not found'

# ---- data blobs ----
class_data = {e['name']: e for e in tooltip}
html, n = re.subn(r'^  const CLASS_DATA = .*$',
                  lambda m: f'  const CLASS_DATA = {jsblob(class_data)};',
                  html, count=1, flags=re.M)
assert n == 1, 'CLASS_DATA line not found'
html, n = re.subn(r'^  let EXTRA_DATA = .*; /\* INJECT_EXTRA_DATA \*/$',
                  lambda m: f'  let EXTRA_DATA = {jsblob(extras)}; /* INJECT_EXTRA_DATA */',
                  html, count=1, flags=re.M)
assert n == 1, 'EXTRA_DATA marker not found'

# ---- footer ----
frontier = meta['frontierKept']
footer_new = f'''<footer>
  Scroll to zoom, drag to pan, double-click to zoom in · keys: <code>/</code> search, <code>+</code>/<code>−</code> zoom, <code>f</code> fit, <code>1</code> actual size, <code>Esc</code> close. Hover/focus a node for a quick preview; click a node to pin its Mathlib structure fields and highlight its relatives (<span class="lg-blue">blue</span> = classes it can be derived from, <span class="lg-green">green</span> = classes derivable from it). Hover an edge for the declaration behind it and strictness witnesses; click the edge to pin them. Dashed node outline = Prop-valued mixin (adds no data); field badges distinguish <em>data</em> from <em>laws</em> and mark defaulted fields. Examples and witnesses record which of 28 standard types (ℕ, ℤ, ℚ, ℝ, ℂ, ℝ≥0, ZMod n, Function.End ℕ, …) have each instance.
  <em>Node set</em>: of the {meta['satisfiedTotal']} single-type-argument, non-deprecated structure classes <code>C</code> with <code>synthInstance (C ℝ)</code> succeeding on mathlib4 master, the {meta['K']} most-referenced ones (by declarations mentioning the class) from the core subject areas Algebra/Order/Topology/Analysis/Ring&nbsp;&amp;&nbsp;Field&nbsp;Theory/Data/Logic/Dynamics, closed under direct <code>extends</code> parents (which adds the notation glue: <code>Zero</code>, <code>Mul</code>, <code>LE</code>, …) — {len(inp['nodes'])} nodes. Cut: MeasureTheory, CategoryTheory, Geometry, <code>Lean.Grind.*</code>, <code>Std.*</code>, core utility classes (<code>BEq</code>, <code>Repr</code>, …) and low-reference exotica ({meta['satisfiedTotal'] - len(inp['nodes'])} classes).
  <em>Edges</em>: <code>extends</code> parents (solid) and derived <code>instance</code>s (dashed), each dashed edge attributed to the one hypothesis that implies all others; transitively reduced (a solid edge is elided only for an all-solid path).
  <em>Amber outline</em> = maximal: no other satisfied class implies it — everything ℝ is, in {len(frontier)} classes: {', '.join(f'<code>{c}</code>' for c in frontier)}.
  Per-class data: <a href="real_tooltip_data.json">real_tooltip_data.json</a>.
</footer>'''
html, n = re.subn(r'<footer>.*?</footer>', lambda m: footer_new, html, count=1, flags=re.S)
assert n == 1, 'footer not found'

out = SITE / 'real_instances.html'
# if a previous output exists, we simply overwrite (template is the original page)
out.write_text(html)
print(f'wrote {out} ({len(html)} bytes)')
