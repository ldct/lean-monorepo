#!/usr/bin/env python3
"""Generate scripts/real_hierarchy.dot from scripts/real_input.json.

Layout conventions match site/normedfield_hierarchy.html: rounded boxes filled
by subject-area cluster, solid edges = `extends` parents, dashed = derived
instances, a Legend cluster of color chips, top label text. Additionally,
maximal ("frontier") classes — those no other satisfied class implies — get a
bold amber outline.

Render with graphviz WASM (no local dot):
    node scripts/render_real_svg.mjs   (needs `npm i @viz-js/viz`; see file)
"""
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
inp = json.load(open(HERE / 'real_input.json'))
meta = inp['meta']
clusters = meta['clusters']
frontier = set(meta['frontierKept'])

AREAS = [   # (key, legend label, fill)
    ('normed',   'analysis / normed',        '#cfe2f3'),
    ('metric',   'metric / uniform',         '#d0e0e3'),
    ('topology', 'topology',                 '#d9ead3'),
    ('topoalg',  'topological algebra',      '#d9d2e9'),
    ('order',    'order',                    '#ead1dc'),
    ('ordalg',   'ordered algebra',          '#fde9d9'),
    ('ringth',   'ring & field theory',      '#f4cccc'),
    ('algebra',  'algebraic hierarchy',      '#fff2cc'),
    ('misc',     'numerics / logic',         '#eeeeee'),
    ('notation', 'notation / operations',    '#ffffff'),
]
FILL = {k: f for k, _, f in AREAS}
FRONTIER_COLOR = '#b45309'

n_nodes = len(inp['nodes'])
n_edges = len(inp['edges'])
label_lines = [
    f'Every type class that ℝ satisfies in Mathlib (leanprover-community/mathlib4 master, July 2026) — {n_nodes} of {meta["satisfiedTotal"]} satisfied classes shown.',
    'An edge from S to T indicates that an instance of T can be derived from an instance of S.',
    'Solid edges: `extends` parents / structure projections.  Dashed edges: derived `instance`s.  Bold amber outline: maximal — no other satisfied class implies it.',
    'Transitively reduced (solid-preferring). Curation: most-referenced classes in core subject areas, closed under `extends`; details in the footer.',
]

def q(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'

out = []
out.append('digraph "real" {')
out.append(f'  graph [label={q(chr(10).join(label_lines))}, labelloc="t", fontsize=20, '
           'fontname="Helvetica,sans-Serif", rankdir=TB, ranksep=0.55, nodesep=0.18, compound=true];')
out.append('  node [shape=box, style="rounded,filled", fontname="Helvetica,sans-Serif", '
           'fontsize=11, height=0.28, margin="0.08,0.03", color=black, penwidth=1];')
out.append('  edge [color="#555555", penwidth=0.8, arrowsize=0.6];')

# legend
out.append('  subgraph cluster_legend {')
out.append('    label="Legend"; fontsize=12; color="#999999";')
prev = None
for i, (key, lab, fill) in enumerate(AREAS):
    nid = f'L{i + 1}'
    out.append(f'    {nid} [label={q(lab)}, fillcolor={q(fill)}, fontsize=10];')
    if prev:
        out.append(f'    {prev} -> {nid} [style=invis];')
    prev = nid
out.append(f'    LFRONTIER [label="maximal: all ℝ is", fillcolor="#ffffff", '
           f'color={q(FRONTIER_COLOR)}, penwidth=2.2, fontsize=10];')
out.append(f'    {prev} -> LFRONTIER [style=invis];')
out.append('    LMIXIN [label="Prop mixin (dashed)", fillcolor="#ffffff", style="rounded,filled,dashed", fontsize=10];')
out.append('    LFRONTIER -> LMIXIN [style=invis];')
out.append('  }')

# clusters with nodes
for key, lab, fill in AREAS:
    members = [n for n in inp['nodes'] if clusters[n] == key]
    if not members:
        continue
    out.append(f'  subgraph cluster_{key} {{')
    out.append(f'    label={q(lab)}; fontsize=13; color="#999999";')
    for n in members:
        extra = f', color={q(FRONTIER_COLOR)}, penwidth=2.2' if n in frontier else ''
        out.append(f'    {q(n)} [fillcolor={q(fill)}{extra}];')
    out.append('  }')

for e in inp['edges']:
    style = ', style=dashed' if e['kind'] == 'dashed' else ''
    out.append(f'  {q(e["s"])} -> {q(e["t"])} [id={q(e["s"] + "__" + e["t"])}{style}];')
out.append('}')

(HERE / 'real_hierarchy.dot').write_text('\n'.join(out) + '\n')
print(f'wrote scripts/real_hierarchy.dot ({n_nodes} nodes, {n_edges} edges)')
