#!/usr/bin/env python3
"""Programmatic checks for the staging-only expanded NormedField page."""
import hashlib, html, json, re, subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SITE=ROOT/'site'
I=json.loads((HERE/'hierarchy_input_staging.json').read_text())
T={x['name']:x for x in json.loads((SITE/'tooltip_data_staging.json').read_text())}
E=json.loads((SITE/'hierarchy_extras_staging.json').read_text())
H=(SITE/'normedfield_hierarchy_staging.html').read_text()
S=(HERE/'hierarchy_staging_rendered.svg').read_text()
nodes=set(I['nodes']); edge_pairs={(e['s'],e['t']) for e in I['edges']}
assert len(I['nodes'])==len(nodes)==117
assert len(I['edges'])==len(edge_pairs)==221
assert sum(e['kind']=='solid' for e in I['edges'])==164
assert sum(e['kind']=='dashed' for e in I['edges'])==57
assert set(T)==nodes==set(E['classes'])
assert len(E['edges'])==221
assert all(e['s'] in nodes and e['t'] in nodes for e in I['edges'])
# Structural completeness against the tooltip's direct-parent source of truth.
expected={(s,p['name']) for s in nodes for p in T[s].get('parents',[]) if p['name'] in nodes}
solid={(e['s'],e['t']) for e in I['edges'] if e['kind']=='solid'}
assert solid==expected, (sorted(expected-solid),sorted(solid-expected))
requested=set('NonAssocRing AddCommGroupWithOne CommSemiring NonAssocCommRing NonUnitalCommRing LeftDistribClass RightDistribClass DivisionMonoid NormedAddGroup SeminormedAddGroup SeminormedCommRing NonUnitalNormedCommRing'.split())
assert requested<=nodes
recursive={'NonAssocCommSemiring','NonUnitalNonAssocCommRing','NonUnitalNonAssocCommSemiring','InvolutiveInv'}
assert recursive<=nodes
canonical={
 ('Ring','NonAssocRing'),('CommRing','NonAssocCommRing'),('CommRing','CommSemiring'),
 ('CommRing','NonUnitalCommRing'),('CommRing','AddCommGroupWithOne'),
 ('Distrib','LeftDistribClass'),('Distrib','RightDistribClass'),
 ('GroupWithZero','DivisionMonoid'),('NormedAddCommGroup','NormedAddGroup'),
 ('SeminormedAddCommGroup','SeminormedAddGroup'),('NormedAddGroup','SeminormedAddGroup'),
 ('NormedCommRing','NonUnitalNormedCommRing'),('NormedCommRing','SeminormedCommRing'),
 ('CommSemiring','NonAssocCommSemiring')}
assert canonical<=edge_pairs
# SVG/page data contract.
svg_nodes=set(re.findall(r'class="node" data-class-name="([^"]+)"',S))
svg_edges=set()
for title in re.findall(r'<g id="[^"]+" class="edge">\s*<title>([^<]+)</title>',S):
    parts=html.unescape(title).split('->')
    if len(parts)==2: svg_edges.add(tuple(parts))
assert svg_nodes==nodes
assert svg_edges==edge_pairs
assert H.count('data-class-name=')==117
assert len(re.findall(r'<g id="[^"]+" class="edge">',H))==221
assert 'INJECT_EXTRA_DATA' in H and 'const CLASS_DATA' in H and 'let FINITE_EX' in H
assert 'STAGING REVIEW' in H
# Production tracked files remain byte-identical to HEAD.
for rel in ['v32/playground/site/normedfield_hierarchy.html','v32/playground/scripts/hierarchy_input.json']:
    path=ROOT.parent.parent/rel
    head=subprocess.run(['git','show',f'HEAD:{rel}'],cwd=ROOT.parent.parent,check=True,capture_output=True).stdout
    assert path.read_bytes()==head, f'production file changed: {rel}'
print('PASS: staging hierarchy checks')
print(f'nodes={len(nodes)} edges={len(edge_pairs)} solid={len(solid)} dashed={len(edge_pairs)-len(solid)}')
