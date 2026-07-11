#!/usr/bin/env python3
"""Programmatic verification of site/real_instances.html (contract + spot checks).

Checks:
  1. the inline <script> parses (written out for `node --check`)
  2. every SVG data-class-name has a CLASS_DATA entry and vice versa
  3. every drawn SVG edge (g.edge > title "S->T") has an EXTRA_DATA.edges entry
     and matches scripts/real_input.json, and vice versa
  4. EXTRA_DATA.classes / fields keys are consistent with CLASS_DATA
  5. roster identical to the NormedField page's roster (28 types)
  6. ℝ satisfies EVERY node (instance matrix column check)
  7. required classes present; NormedField present and not maximal
  8. every edge has a resolved backing decl
Run: python3 scripts/verify_real_page.py
"""
import html as htmlmod
import json
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
SITE = HERE.parent / 'site'
page = (SITE / 'real_instances.html').read_text()
inp = json.load(open(HERE / 'real_input.json'))
fails = []

def check(name, cond, detail=''):
    print(('PASS' if cond else 'FAIL'), name, detail if not cond else '')
    if not cond:
        fails.append(name)

# ---- 1. inline script parses ----
scripts = re.findall(r'<script>\n(.*?)</script>', page, flags=re.S)
check('exactly one inline script', len(scripts) == 1, f'found {len(scripts)}')
tmp = HERE / '.verify_inline.js'
tmp.write_text(scripts[0])
r = subprocess.run(['node', '--check', str(tmp)], capture_output=True, text=True)
check('node --check inline script', r.returncode == 0, r.stderr[:400])
tmp.unlink()

# ---- extract blobs ----
class_data = json.loads(re.search(r'^  const CLASS_DATA = (.*);$', page, flags=re.M).group(1).replace('<\\/', '</'))
extra = json.loads(re.search(r'^  let EXTRA_DATA = (.*); /\* INJECT_EXTRA_DATA \*/$', page, flags=re.M).group(1).replace('<\\/', '</'))

# ---- 2. node contract ----
svg_nodes = {htmlmod.unescape(m) for m in re.findall(r'data-class-name="([^"]*)"', page)}
check('SVG nodes == CLASS_DATA keys', svg_nodes == set(class_data),
      f'svg-only={sorted(svg_nodes - set(class_data))[:5]} data-only={sorted(set(class_data) - svg_nodes)[:5]}')
check('SVG nodes == input nodes', svg_nodes == set(inp['nodes']))

# ---- 3. edge contract ----
svg_edges = set()
for m in re.finditer(r'<g id="[^"]*" class="edge">\s*<title>([^<]*)</title>', page):
    t = htmlmod.unescape(m.group(1))
    if '->' in t:
        s, d = t.split('->')
        svg_edges.add((s, d))
input_edges = {(e['s'], e['t']) for e in inp['edges']}
extra_edges = {tuple(k.split('->')) for k in extra['edges']}
check('SVG edges == input edges', svg_edges == input_edges,
      f'svg-only={sorted(svg_edges - input_edges)[:5]} input-only={sorted(input_edges - svg_edges)[:5]}')
check('SVG edges == EXTRA_DATA edges', svg_edges == extra_edges,
      f'svg-only={sorted(svg_edges - extra_edges)[:5]} extra-only={sorted(extra_edges - svg_edges)[:5]}')
check('edge endpoints are drawn nodes',
      all(s in svg_nodes and t in svg_nodes for s, t in svg_edges))

# ---- 4. extras/class consistency ----
check('EXTRA_DATA.classes keys == CLASS_DATA keys', set(extra['classes']) == set(class_data))
proj_keys = {f['proj'] for e in class_data.values() for f in e['ownFields']}
missing_fields = proj_keys - set(extra['fields'])
check('every ownField has an EXTRA_DATA.fields entry', not missing_fields, sorted(missing_fields)[:8])

# ---- 5. roster ----
orig_roster = json.load(open(HERE / 'hierarchy_input.json'))['roster']
check('roster == NormedField page roster (28)', extra['roster'] == orig_roster and len(orig_roster) == 28)

# ---- 6. ℝ column complete ----
r_idx = next(i for i, r in enumerate(extra['roster']) if r['term'] == 'ℝ')
not_r = [c for c, v in extra['classes'].items() if r_idx not in v['insts']]
check('ℝ satisfies every drawn node', not not_r, not_r[:10])

# ---- 7. spot checks ----
for cls in ['Field', 'ConditionallyCompleteLinearOrder', 'CompleteSpace', 'NormedField',
            'RCLike', 'LinearOrder', 'TopologicalSpace', 'UniformSpace', 'MetricSpace',
            'Zero', 'One', 'Mul', 'Add', 'T2Space', 'Archimedean', 'EuclideanDomain', 'CharZero']:
    check(f'node present: {cls}', cls in svg_nodes)
frontier = set(inp['meta']['frontierKept'])
check('NormedField NOT maximal', 'NormedField' not in frontier)
check('something stronger than NormedField kept (RCLike maximal)', 'RCLike' in frontier)

# ---- 8. edge decls resolved ----
undecl = [k for k, v in extra['edges'].items() if not v.get('decl')]
check('every edge has a backing decl', not undecl, undecl[:8])
solid_in = {(e['s'], e['t']) for e in inp['edges'] if e['kind'] == 'solid'}
kind_mismatch = [k for k, v in extra['edges'].items()
                 if (tuple(k.split('->')) in solid_in) != (v['kind'] == 'solid')]
check('edge kinds consistent input<->extras', not kind_mismatch, kind_mismatch[:8])

print()
print('ALL CHECKS PASSED' if not fails else f'{len(fails)} FAILURES: {fails}')
sys.exit(1 if fails else 0)
