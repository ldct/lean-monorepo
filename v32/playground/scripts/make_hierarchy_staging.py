#!/usr/bin/env python3
"""Build every staging-only artifact for the expanded NormedField hierarchy.

The input expansion is derived from the production curation plus the v4.31
full-discovery parent/instance data. Parent declarations were cross-checked
against the repository's pinned v4.32 source. The four NSMul/NPow/ZSMul/ZPow
parent edges added in v4.32 are retained from the production input.

Requires Graphviz `dot` and, for regenerating metadata, Lean/lake.
Does not modify production input/page/artifacts.
"""
import html, json, re, subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PROD=json.loads((HERE/'hierarchy_input.json').read_text())
DISC=json.loads((ROOT.parent.parent/'v31/playground/scripts/real_discovery.json').read_text())
SAT={x['name']:x for x in DISC['satisfied']}
SEEDS=set('NonAssocRing AddCommGroupWithOne CommSemiring NonAssocCommRing NonUnitalCommRing LeftDistribClass RightDistribClass DivisionMonoid NormedAddGroup SeminormedAddGroup SeminormedCommRing NonUnitalNormedCommRing'.split())
old=set(PROD['nodes']); selected=old|SEEDS
while True:
    nxt=selected|{p for n in selected for p in SAT.get(n,{}).get('parents',[]) if p in SAT}
    if nxt==selected: break
    selected=nxt
added=selected-old
prod_cats=json.loads((HERE/'hierarchy_node_categories.json').read_text())
def category(n):
    if n in prod_cats: return prod_cats[n]
    m=SAT[n]['module']
    return 'normed' if m.startswith('Mathlib.Analysis') else 'algebra'
new_nodes=sorted(added,key=lambda n:(category(n),n))
nodes=PROD['nodes']+new_nodes
solid={(s,t) for s in selected for t in SAT.get(s,{}).get('parents',[]) if t in selected}
# These are direct v4.32 parents but absent from the v4.31 discovery snapshot.
solid |= {(e['s'],e['t']) for e in PROD['edges'] if e['kind']=='solid'}
derived={(e['s'],e['t']) for e in PROD['edges'] if e['kind']=='dashed'}
canon={}
for e in DISC['instEdges']:
    if len(e['hyps'])!=1: continue
    s,t=e['hyps'][0],e['d']
    if s in selected and t in selected and (s in added or t in added) and (s,t) not in solid:
        canon.setdefault((s,t),e['inst'])
edges=[{'s':s,'t':t,'kind':'solid'} for s,t in sorted(solid,key=lambda e:(nodes.index(e[0]),nodes.index(e[1])))]
for e in PROD['edges']:
    if e['kind']=='dashed': edges.append(dict(e))
for (s,t),decl in sorted(canon.items(),key=lambda kv:(nodes.index(kv[0][0]),nodes.index(kv[0][1]))):
    if (s,t) not in derived: edges.append({'s':s,'t':t,'kind':'dashed','decl':decl})
out={k:v for k,v in PROD.items() if k not in ('nodes','edges','owners')}
out={'nodes':nodes,'edges':edges,'owners':nodes,**out}
(HERE/'hierarchy_input_staging.json').write_text(json.dumps(out,ensure_ascii=False,indent=1)+'\n')
cats=dict(prod_cats); cats.update({n:category(n) for n in new_nodes})
(HERE/'hierarchy_node_categories_staging.json').write_text(json.dumps(cats,ensure_ascii=False,indent=1)+'\n')
subprocess.run(['python3',str(HERE/'gen_hierarchy_staging.py')],check=True)
raw=subprocess.run(['dot','-Tsvg',str(HERE/'hierarchy_staging.dot')],check=True,capture_output=True,text=True).stdout
raw=re.sub(r'^[\s\S]*?(?=<svg)','',raw)
def annotate(m):
    title=html.unescape(m.group(3))
    if re.fullmatch(r'L\d+',title): return m.group(0)
    a=html.escape(title,quote=True)
    return f'{m.group(1)} data-class-name="{a}" tabindex="0" role="img" aria-label="{a}"{m.group(2)}{m.group(3)}{m.group(4)}'
svg,n=re.subn(r'(<g id="[^"]*" class="node")(>\s*<title>)([^<]*)(</title>)',annotate,raw)
if n!=len(nodes)+6: raise SystemExit(f'annotated {n}, expected {len(nodes)+6} nodes including legend')
(HERE/'hierarchy_staging_rendered.svg').write_text(svg)
# Regenerate staging-only metadata with the pinned v4.32 environment before
# assembling the page. The extractors verify all direct parents/edge backings.
subprocess.run(['lake','env','lean','scripts/extract_tooltip_data_staging.lean'],cwd=ROOT,check=True)
subprocess.run(['lake','env','lean','scripts/extract_hierarchy_extras_staging.lean'],cwd=ROOT,check=True)
subprocess.run(['python3',str(HERE/'build_hierarchy_staging_page.py')],check=True)
print(f'complete: {len(nodes)} nodes, {len(edges)} edges; added {len(new_nodes)} recursive/new nodes')
