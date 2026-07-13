# NormedField hierarchy figure: how it's made

`site/normedfield_hierarchy.html` shows the typeclass hierarchy underlying
`NormedField` in Mathlib (pinned at v4.32.0-rc1-patch1), an analogue of Fig. 1
of *The Lean Mathematical Library* (CPP '20).

## The drawing is hand-curated, not auto-discovered

The graph's structure — 101 nodes and 143 edges — is the hand-curated list in
`scripts/hierarchy_input.json`. It is **not** computed from Mathlib. Every
listed edge is *source-verified* against the pinned Mathlib by
`extract_hierarchy_extras.lean` (the extraction fails loudly on an edge whose
backing `extends` parent or `instance` declaration it cannot resolve — see
`edges resolved: 143/143` in its log), so the figure never draws a false
arrow. But verification only covers edges that are listed: **an arrow missing
from the drawing may still exist in Mathlib.**

That matters because the page treats the drawn graph as the source of truth
for reachability: the blue/green relative highlighting when a node is pinned,
and the "sharp examples — go no higher" computation in the tooltips, both walk
the drawn edges only. A missing edge therefore shows up as a mathematically
wrong "unrelated" verdict, not just a sparser picture. A real instance of
this: `Ring → NonUnitalRing` (Mathlib's `Ring.toNonUnitalRing`) was absent
until it was noticed that pinning `Ring` left `NonUnitalRing` faded, with no
drawn path between them; edge 143 fixed it.

Deliberate omissions do exist: transitively derivable arrows and some arrows
to the leaves (e.g. `Distrib → Mul`) are left out for readability, matching
the original figure's editorial choices. The rule of thumb: an edge S → T may
be omitted only when the drawn graph already contains a directed path from S
to T. If there is no path at all, the omission is a bug in the curation —
add the edge.

## Pipeline

Node categories/colors live in `hierarchy_node_categories.json`; the roster of
standard types used for examples and strictness witnesses lives in
`hierarchy_input.json` (`roster`).

1. **Edit** `scripts/hierarchy_input.json` (nodes, edges, roster). An edge may
   set `"constraint": false` to be drawn without influencing rank assignment.
2. **Dot**: `python3 scripts/gen_hierarchy_dot.py` → `scripts/hierarchy.dot`.
3. **SVG**: `NODE_PATH=<dir with @viz-js/viz> node scripts/render_hierarchy_svg.mjs`
   → `scripts/hierarchy_rendered.svg` (graphviz WASM; adds the
   `data-class-name` attributes the page JS binds to). **But see the layout
   caveat below before splicing this into the page.**
4. **Extract**: `lake env lean scripts/extract_hierarchy_extras.lean`
   → `site/hierarchy_extras.json`. Verifies all edges, resolves each edge's
   backing declaration for the edge tooltips, and computes per-roster-type
   instance sets (watch the per-type `roster X: N classes` log lines — a
   roster term that fails to elaborate silently reports 0).
5. **Inject**: `python3 scripts/inject_extras.py` inlines the JSON into the
   page (`EXTRA_DATA`). Idempotent.

## Finite-example playground links (`finite example ↗`)

Alongside the `instance skeleton ↗` link, a node's tooltip may offer a
`finite example ↗` link opening `live.lean-lang.org` on a **small finite type
that is an instance of exactly that class and nothing higher** — every law
proved by `by decide`, with a short usage example touching only that class's
API. The full curated zoo lives (and is source-verified) in
`Playground/FiniteExemplars.lean`; the per-node playground snippets are a
separate, self-contained curation:

1. **Author/verify** the snippets in `scripts/gen_finite_exemplars.py`, then
   `python3 scripts/gen_finite_exemplars.py` → `site/finite_exemplars.json`.
2. **Compile-check** every snippet standalone (as it will appear on lean-live):
   `bash scripts/check_finite_exemplars.sh` (expects all `PASS`).
3. **Inject**: `python3 scripts/inject_finite_exemplars.py` inlines the JSON
   into the page (`FINITE_EX`). Idempotent. The link renders only for the ~20
   nodes that have a curated exemplar.

## Layout caveat: the page's SVG is not the pipeline's SVG

The inline SVG in `site/normedfield_hierarchy.html` (2403×941pt) is the
original rendering made with **system graphviz 2.43.0**, whose layout of this
dot file is far more compact than anything current renderers produce: both
the viz-js WASM build and system graphviz 15.x render the same graph at
~6400×1450pt. The difference is the invisible layout clusters
(`style=invis` subgraphs grouping the metric/normed/topological nodes) —
2.43.0 packed them tightly; modern graphviz spreads them out. Dropping the
clusters entirely gets modern graphviz down to ~1920×1109pt, at the cost of
the deliberate spatial grouping.

Consequently, small graph edits are best made by **hand-patching the page's
inline SVG** rather than re-rendering: the `Ring → NonUnitalRing` arrow
(edge 143) was added this way, as a dashed `<g class="edge">` with a
`<title>Ring&#45;&gt;NonUnitalRing</title>` (the page JS builds its adjacency
and hover targets from those titles, so a hand-added edge gets tooltips and
highlighting for free). Re-render from the pipeline only if you accept a
different, wider layout — or first reproduce the 2.43.0 rendering.

Class/field tooltip data (`CLASS_DATA`) has its own extractor
(`extract_tooltip_data.lean` → `inject_class_data.py` →
`fix_added_over_parents.py`) and only needs rerunning when the node set or
the Mathlib pin changes.
