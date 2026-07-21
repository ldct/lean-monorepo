#!/usr/bin/env python3
"""Programmatic checks for the staging-only expanded NormedField page."""
import hashlib, html, json, re, subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SITE=ROOT/'site'
I=json.loads((HERE/'hierarchy_input_staging.json').read_text())
D=json.loads((HERE/'hierarchy_discovery_staging.json').read_text())
T={x['name']:x for x in json.loads((SITE/'tooltip_data_staging.json').read_text())}
E=json.loads((SITE/'hierarchy_extras_staging.json').read_text())
H=(SITE/'normedfield_hierarchy_staging.html').read_text()
S=(HERE/'hierarchy_staging_rendered.svg').read_text()
nodes=set(I['nodes'])
edge_pairs={(e['s'],e['t']) for e in I['edges']}
solid={(e['s'],e['t']) for e in I['edges'] if e['kind']=='solid'}
dashed={(e['s'],e['t']) for e in I['edges'] if e['kind']=='dashed'}
assert len(I['nodes'])==len(nodes)
assert len(I['edges'])==len(edge_pairs)
assert not any('Lean.Grind' in n for n in nodes)
assert set(T)==nodes==set(E['classes'])
assert len(E['edges'])==len(I['edges'])
assert all(e['s'] in nodes and e['t'] in nodes for e in I['edges'])
assert I['meta']['mathlibRev']==D['mathlibRev']=='81a5d257c8e410db227a6665ed08f64fea08e997'
assert I['meta']['excludedNameSubstring']=='Lean.Grind'
assert I['meta']['transitiveReduction'] is False

# Structural completeness against the v4.32 tooltip extractor's direct-parent
# source of truth, including all direct arrows (not just parent closure).
expected_solid={(s,p['name']) for s in nodes for p in T[s].get('parents',[])}
assert solid==expected_solid, (sorted(expected_solid-solid),sorted(solid-expected_solid))

# Recursive closure and complete direct unary-instance relation against the
# committed v4.32 discovery output.  Excluded Lean.Grind targets are the only
# permitted outgoing omissions.
unary=[e for e in D['unaryInstances'] if e['source'] in nodes]
eligible_unary={(e['source'],e['target']) for e in unary if 'Lean.Grind' not in e['target']}
excluded_direct={e['target'] for e in unary if 'Lean.Grind' in e['target']}
excluded=set(I['meta']['excludedReachableClasses'])
assert excluded_direct <= excluded
assert all(t in nodes for _,t in eligible_unary)
assert all(p['name'] in nodes or 'Lean.Grind' in p['name']
           for s in nodes for p in T[s].get('parents',[]))
# A unary relation represented by a direct parent is solid; every other one is dashed.
assert eligible_unary-solid <= dashed, sorted((eligible_unary-solid)-dashed)
assert set(I['meta']['excludedReachableClasses'])==excluded
assert excluded and all('Lean.Grind' in n for n in excluded)
# Production curated dashed implications remain represented.
P=json.loads((HERE/'hierarchy_input.json').read_text())
curated={(e['s'],e['t']) for e in P['edges'] if e['kind']=='dashed'}
assert curated <= edge_pairs

# Every dashed edge has a source-verified backing declaration in extracted metadata.
assert all(E['edges'][f"{s}->{t}"]['decl'] for s,t in dashed)

# SVG/page data contract.
svg_nodes=set(re.findall(r'class="node" data-class-name="([^"]+)"',S))
svg_edges=set()
for title in re.findall(r'<g id="[^"]+" class="edge">\s*<title>([^<]+)</title>',S):
    parts=html.unescape(title).split('->')
    if len(parts)==2: svg_edges.add(tuple(parts))
assert svg_nodes==nodes
assert svg_edges==edge_pairs
assert H.count('data-class-name=')==len(nodes)
assert len(re.findall(r'<g id="[^"]+" class="edge">',H))==len(edge_pairs)
assert 'INJECT_EXTRA_DATA' in H and 'const CLASS_DATA' in H and 'let FINITE_EX' in H
assert 'STAGING REVIEW' in H and 'Lean.Grind' in H
assert not any(f'data-class-name="{n}"' in H for n in excluded)

# Production tracked files remain byte-identical to HEAD.
for rel in [
    'v32/playground/site/normedfield_hierarchy.html',
    'v32/playground/scripts/hierarchy_input.json',
]:
    path=ROOT.parent.parent/rel
    head=subprocess.run(['git','show',f'HEAD:{rel}'],cwd=ROOT.parent.parent,
                        check=True,capture_output=True).stdout
    assert path.read_bytes()==head, f'production file changed: {rel}'
print('PASS: staging hierarchy checks')
print(f'nodes={len(nodes)} edges={len(edge_pairs)} solid={len(solid)} dashed={len(dashed)}')
print(f'eligible unary pairs={len(eligible_unary)} excluded Lean.Grind classes={len(excluded)}')
