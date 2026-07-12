#!/usr/bin/env python3
"""Generate scripts/hierarchy.dot for the NormedField hierarchy page from
scripts/hierarchy_input.json (nodes + edges; every edge is source-verified
against the pinned Mathlib by extract_hierarchy_extras.lean).

Recreates the lost original generator. Graph structure comes from the input
JSON; everything else here (category colors, legend, captions) is editorial
presentation, matched to the original figure. Render the dot with
render_hierarchy_svg.mjs (graphviz WASM; the original figure was rendered
with system graphviz 2.43.0, so coordinates differ across renderers even
though the drawn graph is the same).
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MATHLIB_PIN = "v4.32.0-rc1-patch1"

CAPTIONS = [
    f"The structure hierarchy underlying NormedField in Mathlib (leanprover-community/mathlib4 {MATHLIB_PIN}).",
    "An edge from S to T indicates that an instance of T can be derived from an instance of S.",
    "Solid edges: `extends` parents / structure projections.  Dashed edges: derived `instance`s.",
    "Transitively derivable arrows and some arrows to the leaves (e.g. Distrib to Mul) are omitted for readability; per-class parents and fields are in tooltip_data.json.",
]

# category -> (fill, legend label); legend chips L1..L6 keep this order
CATEGORIES = {
    "normed":   ("#cfe2f3", "normed structures"),
    "metric":   ("#d9ead3", "metric / topology"),
    "topoalg":  ("#d0e0e3", "topological algebra"),
    "ringth":   ("#f4cccc", "ring-theoretic props"),
    "algebra":  ("#fff2cc", "algebraic hierarchy"),
    "notation": ("#ffffff", "notation / operations"),
}

# invisible layout clusters, by category (algebra/notation are unclustered)
CLUSTERS = {"metric": "topo", "topoalg": "topoalg", "normed": "normed", "ringth": "ringth"}

NODE_CATEGORY = json.loads((HERE / "hierarchy_node_categories.json").read_text())


def esc(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def main() -> None:
    data = json.loads((HERE / "hierarchy_input.json").read_text())
    nodes, edges = data["nodes"], data["edges"]

    missing = [n for n in nodes if n not in NODE_CATEGORY]
    if missing:
        raise SystemExit(f"nodes without a category (add to hierarchy_node_categories.json): {missing}")

    out = []
    out.append('digraph mathlib {')
    label = "\\n".join(esc(c) for c in CAPTIONS)
    out.append(f'  label="{label}"; labelloc=t; fontname="Helvetica"; fontsize=20;')
    out.append('  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=11, color=black];')
    out.append('  edge [color="#555555", penwidth=0.8, arrowsize=0.5];')

    out.append('  subgraph cluster_legend {')
    out.append('    label="Legend"; fontsize=12; color="#999999"; style=rounded;')
    for i, (fill, text) in enumerate(CATEGORIES.values(), start=1):
        out.append(f'    L{i} [label="{esc(text)}", fillcolor="{fill}"];')
    for i in range(1, len(CATEGORIES)):
        out.append(f'    L{i} -> L{i + 1} [style=invis];')
    out.append('  }')

    by_cluster = {}
    for n in nodes:
        by_cluster.setdefault(CLUSTERS.get(NODE_CATEGORY[n]), []).append(n)

    def node_line(n, indent):
        fill = CATEGORIES[NODE_CATEGORY[n]][0]
        return f'{indent}"{n}" [fillcolor="{fill}"];'

    for cluster, members in sorted(by_cluster.items(), key=lambda kv: kv[0] or ""):
        if cluster is None:
            for n in members:
                out.append(node_line(n, "  "))
        else:
            out.append(f'  subgraph cluster_{cluster} {{')
            out.append('    style=invis;')
            for n in members:
                out.append(node_line(n, "    "))
            out.append('  }')

    for e in edges:
        attrs = ' [style=dashed]' if e["kind"] == "dashed" else ""
        out.append(f'  "{e["s"]}" -> "{e["t"]}"{attrs};')

    out.append('}')
    (HERE / "hierarchy.dot").write_text("\n".join(out) + "\n")
    print(f"wrote scripts/hierarchy.dot ({len(nodes)} nodes, {len(edges)} edges)")


if __name__ == "__main__":
    main()
