#!/usr/bin/env python3
"""Generate the staging-only expanded NormedField hierarchy DOT file.

Input:  scripts/hierarchy_input_staging.json
Output: scripts/hierarchy_staging.dot
Production hierarchy files are never read as output targets or modified.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MATHLIB_PIN = "v4.32.0 · commit 81a5d257"
CAPTIONS = [
    f"STAGING REVIEW — expanded structural hierarchy underlying NormedField in Mathlib ({MATHLIB_PIN}).",
    "An edge from S to T indicates that an instance of T can be derived from an instance of S.",
    "Solid edges: every direct `extends` parent in the selected set.  Dashed edges: curated/canonical derived `instance`s.",
    "The staging node set is closed recursively under direct parents; transitive direct-parent arrows are intentionally retained.",
]
CATEGORIES = {
    "normed": ("#cfe2f3", "normed structures"),
    "metric": ("#d9ead3", "metric / topology"),
    "topoalg": ("#d0e0e3", "topological algebra"),
    "ringth": ("#f4cccc", "ring-theoretic props"),
    "algebra": ("#fff2cc", "algebraic hierarchy"),
    "notation": ("#ffffff", "notation / operations"),
}
CLUSTERS = {"metric": "topo", "topoalg": "topoalg", "normed": "normed", "ringth": "ringth"}

def esc(s): return s.replace("\\", "\\\\").replace('"', '\\"')

def main():
    data = json.loads((HERE / "hierarchy_input_staging.json").read_text())
    categories = json.loads((HERE / "hierarchy_node_categories_staging.json").read_text())
    nodes, edges = data["nodes"], data["edges"]
    missing = [n for n in nodes if n not in categories]
    if missing: raise SystemExit(f"nodes without staging category: {missing}")
    out = ["digraph mathlib_staging {"]
    out.append(f'  label="{"\\n".join(esc(c) for c in CAPTIONS)}"; labelloc=t; fontname="Helvetica"; fontsize=20;')
    out.append('  graph [ranksep=0.58, nodesep=0.22];')
    out.append('  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=11, color=black];')
    out.append('  edge [color="#555555", penwidth=0.8, arrowsize=0.5];')
    out.append('  subgraph cluster_legend {')
    out.append('    label="Legend"; fontsize=12; color="#999999"; style=rounded;')
    for i,(fill,text) in enumerate(CATEGORIES.values(),1): out.append(f'    L{i} [label="{esc(text)}", fillcolor="{fill}"];')
    for i in range(1,len(CATEGORIES)): out.append(f'    L{i} -> L{i+1} [style=invis];')
    out.append('  }')
    by_cluster={}
    for n in nodes: by_cluster.setdefault(CLUSTERS.get(categories[n]),[]).append(n)
    def line(n,indent): return f'{indent}"{n}" [fillcolor="{CATEGORIES[categories[n]][0]}"];'
    for cluster,members in sorted(by_cluster.items(),key=lambda kv:kv[0] or ""):
        if cluster is None:
            out.extend(line(n,"  ") for n in members)
        else:
            out.append(f'  subgraph cluster_{cluster} {{'); out.append('    style=invis;')
            out.extend(line(n,"    ") for n in members); out.append('  }')
    for e in edges:
        attrs=[]
        if e["kind"]=="dashed": attrs.append("style=dashed")
        if not e.get("constraint",True): attrs.append("constraint=false")
        suffix=f' [{", ".join(attrs)}]' if attrs else ""
        out.append(f'  "{e["s"]}" -> "{e["t"]}"{suffix};')
    out.append('}')
    path=HERE/"hierarchy_staging.dot"; path.write_text("\n".join(out)+"\n")
    print(f"wrote {path.name} ({len(nodes)} nodes, {len(edges)} edges)")
if __name__ == "__main__": main()
