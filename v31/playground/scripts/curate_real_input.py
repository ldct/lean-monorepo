#!/usr/bin/env python3
"""Curate scripts/real_discovery.json into scripts/real_input.json for the
"type classes ℝ satisfies" diagram (site/real_instances.html).

CURATION RULE (documented in the page footer; keep in sync):
  1. Universe: every non-deprecated structure class `C` with exactly one
     explicit `Type u` argument (all other binders instance-implicit) such that
     `synthInstance (C ℝ)` succeeds — computed by scripts/discover_real_classes.lean.
  2. Subject filter: classes defined in modules under Mathlib.{Algebra,
     Analysis, Data, Dynamics, FieldTheory, GroupTheory, LinearAlgebra, Logic,
     Order, RingTheory, Topology}.  (This cuts MeasureTheory, CategoryTheory,
     Geometry, Combinatorics, AlgebraicTopology, Lean.Grind.*, Std.*, and core
     utility classes like BEq/Repr/SizeOf.)
  3. Prominence filter: rank the step-2 classes by the number of declarations
     in the environment whose *statement* mentions the class; keep the top K.
  4. Glue closure: close the step-3 set under direct `extends` parents within
     the satisfied universe (this re-adds notation classes like Zero/Mul/LE
     even when they are defined outside Mathlib).
  K is chosen so the final node count lands near TARGET (~200).

EDGES:
  solid  = direct `extends` parents between kept nodes;
  dashed = derived instances `∀ α [C₁ α]…[Cₖ α], D α`, attributed to the
     hypothesis H whose implication closure covers all other hypotheses
     (closure = extends ∪ class-context binders ∪ already-attributed edges,
     iterated to a fixpoint), drawn H → D with the backing instance recorded;
  then transitively reduced, solid-preferring: a solid edge is elided only if
  an all-solid alternative path exists; a dashed edge if any alternative path
  exists.  Intra-SCC (mutual-implication) edges are never elided.

FRONTIER ("everything ℝ is"): satisfied classes not implied by any other
satisfied class — no satisfied class extends them, and no recorded instance
(all of whose hypotheses ℝ satisfies) yields them.
"""
import json
import pathlib
import sys
from collections import defaultdict

HERE = pathlib.Path(__file__).resolve().parent
TARGET = 200

ALLOW = ('Mathlib.Algebra', 'Mathlib.Analysis', 'Mathlib.Data', 'Mathlib.Dynamics',
         'Mathlib.FieldTheory', 'Mathlib.GroupTheory', 'Mathlib.LinearAlgebra',
         'Mathlib.Logic', 'Mathlib.Order', 'Mathlib.RingTheory', 'Mathlib.Topology')

disc = json.load(open(HERE / 'real_discovery.json'))
sat = {c['name']: c for c in disc['satisfied']}
satset = set(sat)
roster = json.load(open(HERE / 'hierarchy_input.json'))['roster']

# ---------- implication machinery over the full satisfied set ----------
parents = {n: [p for p in sat[n]['parents'] if p in satset and p != n] for n in satset}
context = {n: [c for c in sat[n]['context'] if c in satset and c != n] for n in satset}

# instances: (inst, d, hyps) with d not in hyps and every hyp in satset
insts = []
for e in disc['instEdges']:
    hyps = sorted(set(e['hyps']))
    if e['d'] in hyps or not hyps:
        continue
    insts.append((e['inst'], e['d'], hyps))
# deterministic, prefer fewer hypotheses then shorter instance names
insts.sort(key=lambda x: (len(x[2]), len(x[0]), x[0]))

def closures(adj):
    memo = {}
    def go(x, stack):
        if x in memo:
            return memo[x]
        if x in stack:          # cycle: fall back to iterative BFS
            return None
        stack = stack | {x}
        out = set()
        ok = True
        for y in adj[x]:
            out.add(y)
            sub = go(y, stack)
            if sub is None:
                ok = False
                break
            out |= sub
        if not ok:              # BFS fallback (handles cycles)
            out, todo = set(), list(adj[x])
            while todo:
                y = todo.pop()
                if y in out:
                    continue
                out.add(y)
                todo.extend(adj[y])
        memo[x] = out
        return out
    return {x: go(x, frozenset()) for x in satset}

# attributed dashed edges via fixpoint
impl_adj = defaultdict(set)          # implication graph: extends ∪ context ∪ attributed
for n in satset:
    impl_adj[n] |= set(parents[n]) | set(context[n])
attributed = {}                      # (s, t) -> backing instance name
while True:
    clo = closures(impl_adj)
    added = False
    for inst, d, hyps in insts:
        for h in hyps:
            if (h, d) in attributed:
                continue
            rest = [x for x in hyps if x != h]
            if all(r == h or r in clo[h] for r in rest):
                attributed[(h, d)] = inst
                if d not in impl_adj[h]:
                    impl_adj[h].add(d)
                    added = True
    if not added:
        break

# frontier over the full satisfied set: implied by extends children or by any
# recorded instance (hypotheses are all satisfied by construction)
implied = set()
for n in satset:
    implied |= set(parents[n])
for _, d, _ in insts:
    implied.add(d)
frontier_all = sorted(satset - implied)

# ---------- curation ----------
core = sorted(n for n in satset if sat[n]['module'].startswith(ALLOW))
core.sort(key=lambda n: (-sat[n]['refCount'], n))

def close_under_parents(seed):
    kept = set(seed)
    todo = list(seed)
    while todo:
        x = todo.pop()
        for p in parents[x]:
            if p not in kept:
                kept.add(p)
                todo.append(p)
    return kept

K = min(TARGET, len(core))
while True:
    kept = close_under_parents(core[:K])
    if len(kept) <= TARGET + 15 or K <= 50:
        break
    K -= 5
print(f'satisfied: {len(satset)}, subject-filtered core: {len(core)}, K: {K}, '
      f'kept after extends-closure: {len(kept)}')
cut = sorted(satset - kept)

# ---------- drawn edges ----------
solid = set()
for n in kept:
    for p in parents[n]:
        if p in kept:
            solid.add((n, p))
dashed = {}
for (s, t), inst in attributed.items():
    if s in kept and t in kept and (s, t) not in solid:
        dashed[(s, t)] = inst
print(f'edges before reduction: solid {len(solid)}, dashed {len(dashed)}')

# ---------- transitive reduction (solid-preferring, SCC-safe) ----------
union_adj = defaultdict(set)
solid_adj = defaultdict(set)
for s, t in solid:
    union_adj[s].add(t)
    solid_adj[s].add(t)
for s, t in dashed:
    union_adj[s].add(t)

def scc(nodes, adj):
    index, low, onstk, stk, out = {}, {}, set(), [], []
    counter = [0]
    sys.setrecursionlimit(100000)
    def strong(v):
        index[v] = low[v] = counter[0]; counter[0] += 1
        stk.append(v); onstk.add(v)
        for w in adj[v]:
            if w not in index:
                strong(w); low[v] = min(low[v], low[w])
            elif w in onstk:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stk.pop(); onstk.discard(w); comp.append(w)
                if w == v:
                    break
            out.append(comp)
    for v in nodes:
        if v not in index:
            strong(v)
    return out

comps = scc(sorted(kept), union_adj)
comp_of = {}
for i, comp in enumerate(comps):
    for v in comp:
        comp_of[v] = i
nontrivial = [c for c in comps if len(c) > 1]
if nontrivial:
    print(f'NOTE: {len(nontrivial)} mutual-implication group(s): {nontrivial}')

def reachable(src, dst, adj, skip_edge):
    todo, seen = list(adj[src] - ({dst} if (src, dst) == skip_edge else set())), set()
    # exclude ONLY the direct edge src->dst; paths through others allowed
    todo = [w for w in adj[src] if not (w == dst)]
    while todo:
        x = todo.pop()
        if x == dst:
            return True
        if x in seen:
            continue
        seen.add(x)
        todo.extend(adj[x])
    return False

kept_edges = []                      # (s, t, kind, decl)
for s, t in sorted(solid):
    if comp_of[s] == comp_of[t] or not reachable(s, t, solid_adj, (s, t)):
        kept_edges.append((s, t, 'solid', None))
for (s, t), inst in sorted(dashed.items()):
    if comp_of[s] == comp_of[t] or not reachable(s, t, union_adj, (s, t)):
        kept_edges.append((s, t, 'dashed', inst))
n_solid = sum(1 for e in kept_edges if e[2] == 'solid')
n_dashed = len(kept_edges) - n_solid
print(f'edges after reduction: solid {n_solid}, dashed {n_dashed}')

# ---------- clusters (by defining module) ----------
def area(n):
    m = sat[n]['module']
    if not m.startswith('Mathlib.'):
        return 'notation'
    if m.startswith('Mathlib.Order'):
        return 'order'
    if m.startswith('Mathlib.Topology.Algebra'):
        return 'topoalg'
    if m.startswith(('Mathlib.Topology.MetricSpace', 'Mathlib.Topology.EMetricSpace',
                     'Mathlib.Topology.UniformSpace', 'Mathlib.Topology.Bornology')):
        return 'metric'
    if m.startswith('Mathlib.Topology'):
        return 'topology'
    if m.startswith('Mathlib.Analysis'):
        return 'normed'
    if m.startswith('Mathlib.Algebra.Order'):
        return 'ordalg'
    if m.startswith(('Mathlib.RingTheory', 'Mathlib.FieldTheory', 'Mathlib.LinearAlgebra')):
        return 'ringth'
    if m.startswith(('Mathlib.Algebra', 'Mathlib.GroupTheory')):
        return 'algebra'
    return 'misc'

clusters = {n: area(n) for n in sorted(kept)}
counts = defaultdict(int)
for n in clusters:
    counts[clusters[n]] += 1
print('cluster sizes:', dict(sorted(counts.items(), key=lambda x: -x[1])))

frontier_kept = sorted(set(frontier_all) & kept)
print(f'frontier (maximal) overall: {len(frontier_all)}, of which kept: {len(frontier_kept)}')

nodes = sorted(kept, key=lambda n: (clusters[n], n))
out = {
    'nodes': nodes,
    'edges': [{'s': s, 't': t, 'kind': k, 'decl': d} for s, t, k, d in kept_edges],
    'owners': nodes,
    'roster': roster,
    'meta': {
        'target': TARGET, 'K': K,
        'satisfiedTotal': len(satset),
        'coreAfterSubjectFilter': len(core),
        'cutClasses': cut,
        'frontierAll': frontier_all,
        'frontierKept': frontier_kept,
        'clusters': clusters,
        'isProp': {n: sat[n]['isProp'] for n in nodes},
        'refCount': {n: sat[n]['refCount'] for n in nodes},
        'sccGroups': nontrivial,
    },
}
(HERE / 'real_input.json').write_text(json.dumps(out, ensure_ascii=False, indent=1))
print(f'wrote scripts/real_input.json: {len(nodes)} nodes, {len(kept_edges)} edges')
