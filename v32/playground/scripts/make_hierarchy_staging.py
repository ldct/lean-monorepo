#!/usr/bin/env python3
"""Build every staging-only artifact for the expanded NormedField hierarchy.

The selected nodes are computed from the existing staging seed set at commit
5597505, using discovery freshly extracted from the pinned Mathlib v4.32.0
environment.  Close recursively under:

* every direct structure (`extends`) parent; and
* every direct unary instance `[Source α] → Target α`.

Classes whose fully-qualified names contain `Lean.Grind` are excluded.  Every
direct parent edge and every discovered unary implication among selected
nodes is retained (no transitive reduction); production curated dashed edges
are retained as well.

Requires Graphviz `dot` and Lean/lake.  Does not modify production input/page
or production metadata artifacts.
"""
import html
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROD = json.loads((HERE / "hierarchy_input.json").read_text())
# The original 117-node staging roster from commit 5597505 is reproducibly
# defined as the production nodes plus these explicit structural additions;
# do not use the generated staging file itself as the seed (that would make
# repeated builds depend on their previous output).
STAGING_SEED_ADDITIONS = set("""
NonAssocRing AddCommGroupWithOne CommSemiring NonAssocCommRing
NonUnitalCommRing LeftDistribClass RightDistribClass DivisionMonoid
NormedAddGroup SeminormedAddGroup SeminormedCommRing
NonUnitalNormedCommRing NonAssocCommSemiring NonUnitalNonAssocCommRing
NonUnitalNonAssocCommSemiring InvolutiveInv
""".split())
DISC_PATH = HERE / "hierarchy_discovery_staging.json"
EXCLUDED_SUBSTRING = "Lean.Grind"
EXPECTED_MATHLIB_REV = "81a5d257c8e410db227a6665ed08f64fea08e997"

# Discovery is part of every build, so the generated staging input cannot
# silently continue to use the old v4.31 snapshot.
subprocess.run(
    ["lake", "env", "lean", "scripts/discover_hierarchy_staging.lean"],
    cwd=ROOT, check=True)
disc = json.loads(DISC_PATH.read_text())
if disc.get("mathlibRev") != EXPECTED_MATHLIB_REV:
    raise SystemExit(f"unexpected discovery Mathlib revision: {disc.get('mathlibRev')}")
classes = {c["name"]: c for c in disc["classes"]}
unary = disc["unaryInstances"]

seed_order = PROD["nodes"] + sorted(
    STAGING_SEED_ADDITIONS - set(PROD["nodes"]),
    key=lambda n: (classes.get(n, {}).get("module", ""), n))

def close(seed, exclude_substring=None):
    selected = set(seed)
    while True:
        add = set()
        for n in selected:
            if n not in classes:
                # A few production nodes are class abbreviations rather than
                # structures; they have no structure parents in the eligible
                # discovery universe and are still valid retained seeds.
                continue
            add.update(classes[n]["parents"])
        add.update(e["target"] for e in unary if e["source"] in selected)
        if exclude_substring is not None:
            add = {n for n in add if exclude_substring not in n}
        add -= selected
        if not add:
            return selected
        selected.update(add)

selected = close(seed_order, EXCLUDED_SUBSTRING)
if any(EXCLUDED_SUBSTRING in n for n in selected):
    raise SystemExit("the staging closure unexpectedly contains an excluded Lean.Grind class")
unrestricted = close(seed_order)
excluded = sorted(n for n in unrestricted if EXCLUDED_SUBSTRING in n)
# In v4.32 the excluded Grind detour introduces no otherwise-unreachable
# non-Grind class. Keep this invariant explicit rather than silently changing
# the interpretation of the filtered closure later.
if unrestricted - set(excluded) != selected:
    raise SystemExit("Lean.Grind-only paths expose non-Grind nodes; define the exclusion policy explicitly")

seed_nodes = set(seed_order)
added = selected - seed_nodes
prod_cats = json.loads((HERE / "hierarchy_node_categories.json").read_text())

def category(n):
    if n in prod_cats:
        return prod_cats[n]
    module = classes[n]["module"]
    if module.startswith("Mathlib.Analysis"):
        return "normed"
    if module.startswith(("Mathlib.Topology.MetricSpace", "Mathlib.Topology.EMetricSpace",
                          "Mathlib.Topology.UniformSpace", "Mathlib.Topology.Metrizable")):
        return "metric"
    if module.startswith(("Mathlib.Topology.Algebra", "Mathlib.Topology.Bornology")):
        return "topoalg"
    if module.startswith(("Mathlib.RingTheory", "Mathlib.FieldTheory", "Mathlib.LinearAlgebra")):
        return "ringth"
    if not module.startswith("Mathlib."):
        return "notation"
    return "algebra"

new_nodes = sorted(added, key=lambda n: (category(n), n))
nodes = seed_order + new_nodes
node_idx = {n: i for i, n in enumerate(nodes)}

# Direct extends edges are complete and intentionally not transitively reduced.
solid = {(s, p) for s in selected for p in classes.get(s, {}).get("parents", [])
         if p in selected}
# Preserve direct v4.32 parents already present in production for retained
# abbrev/non-discovery seeds (notably notation classes changed in v4.32).
solid |= {(e["s"], e["t"]) for e in PROD["edges"] if e["kind"] == "solid"}

# Preserve the production editorial dashed edges (including the handful of
# legitimate multi-hop implications), then add the complete direct unary
# relation among selected nodes.  Solid wins if the same implication is both.
curated = {}
for e in PROD["edges"]:
    if e["kind"] == "dashed" and e["s"] in selected and e["t"] in selected:
        curated[(e["s"], e["t"])] = dict(e)
unary_decls = {(e["source"], e["target"]): e["decl"] for e in unary
               if e["source"] in selected and e["target"] in selected}

edges = [{"s": s, "t": t, "kind": "solid"}
         for s, t in sorted(solid, key=lambda e: (node_idx[e[0]], node_idx[e[1]]))]
for pair in sorted(set(curated) | set(unary_decls), key=lambda e: (node_idx[e[0]], node_idx[e[1]])):
    if pair in solid:
        continue
    if pair in curated:
        edge = curated[pair]
        # Back the edge explicitly when it is also a direct unary implication.
        if pair in unary_decls:
            edge["decl"] = unary_decls[pair]
        edges.append(edge)
    else:
        s, t = pair
        edges.append({"s": s, "t": t, "kind": "dashed", "decl": unary_decls[pair]})

out = {k: v for k, v in PROD.items() if k not in ("nodes", "edges", "owners", "meta")}
out = {
    "nodes": nodes,
    "edges": edges,
    "owners": nodes,
    **out,
    "meta": {
        "mathlibRev": EXPECTED_MATHLIB_REV,
        "seedCommit": "5597505",
        "closure": ["direct extends parents", "direct unary instances [Source α] → Target α"],
        "transitiveReduction": False,
        "excludedNameSubstring": EXCLUDED_SUBSTRING,
        "excludedReachableClasses": excluded,
        "addedSinceSeed": new_nodes,
    },
}
(HERE / "hierarchy_input_staging.json").write_text(
    json.dumps(out, ensure_ascii=False, indent=1) + "\n")
cats = dict(prod_cats)
cats.update({n: category(n) for n in nodes if n not in cats})
(HERE / "hierarchy_node_categories_staging.json").write_text(
    json.dumps(cats, ensure_ascii=False, indent=1) + "\n")

subprocess.run(["python3", str(HERE / "gen_hierarchy_staging.py")], check=True)
raw = subprocess.run(
    ["dot", "-Tsvg", str(HERE / "hierarchy_staging.dot")],
    check=True, capture_output=True, text=True).stdout
raw = re.sub(r"^[\s\S]*?(?=<svg)", "", raw)

def annotate(m):
    title = html.unescape(m.group(3))
    if re.fullmatch(r"L\d+", title):
        return m.group(0)
    attr = html.escape(title, quote=True)
    return (f'{m.group(1)} data-class-name="{attr}" tabindex="0" role="img" '
            f'aria-label="{attr}"{m.group(2)}{m.group(3)}{m.group(4)}')

svg, n = re.subn(
    r'(<g id="[^"]*" class="node")(>\s*<title>)([^<]*)(</title>)', annotate, raw)
if n != len(nodes) + 6:
    raise SystemExit(f"annotated {n}, expected {len(nodes) + 6} nodes including legend")
(HERE / "hierarchy_staging_rendered.svg").write_text(svg)

subprocess.run(
    ["lake", "env", "lean", "scripts/extract_tooltip_data_staging.lean"],
    cwd=ROOT, check=True)
subprocess.run(
    ["lake", "env", "lean", "scripts/extract_hierarchy_extras_staging.lean"],
    cwd=ROOT, check=True)
subprocess.run(["python3", str(HERE / "build_hierarchy_staging_page.py")], check=True)
print(f"complete: {len(nodes)} nodes, {len(edges)} edges; "
      f"added {len(new_nodes)} nodes; excluded {len(excluded)} Lean.Grind classes")
