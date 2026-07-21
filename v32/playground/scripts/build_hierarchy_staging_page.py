#!/usr/bin/env python3
"""Assemble the staging-only interactive NormedField hierarchy review page.

Reads staging-specific SVG and Lean-generated metadata, then copies the
production UI shell and replaces only its inline data/SVG. It never modifies
production hierarchy_input.json or site/normedfield_hierarchy.html.
"""
import json, re
from pathlib import Path

HERE=Path(__file__).resolve().parent
SITE=HERE.parent/'site'
INPUT=json.loads((HERE/'hierarchy_input_staging.json').read_text())
NODES=INPUT['nodes']; EDGES=INPUT['edges']; META=INPUT.get('meta',{})
N_SOLID=sum(e['kind']=='solid' for e in EDGES)
N_DASHED=len(EDGES)-N_SOLID
N_EXCLUDED=len(META.get('excludedReachableClasses',[]))
PROD_HTML=SITE/'normedfield_hierarchy.html'
OUT_HTML=SITE/'normedfield_hierarchy_staging.html'
SVG_PATH=HERE/'hierarchy_staging_rendered.svg'
TT_PATH=SITE/'tooltip_data_staging.json'
EX_PATH=SITE/'hierarchy_extras_staging.json'

entries=json.loads(TT_PATH.read_text())
class_data={e['name']:e for e in entries}
extra=json.loads(EX_PATH.read_text())
if set(class_data)!=set(NODES):
    raise SystemExit('staging tooltip metadata does not match the staging node set')
if set(extra.get('classes',{}))!=set(NODES):
    raise SystemExit('staging extra metadata does not match the staging node set')
if len(extra.get('edges',{}))!=len(EDGES):
    raise SystemExit('staging edge metadata does not match the staging edge set')

page=PROD_HTML.read_text()
svg=SVG_PATH.read_text()
page,n=re.subn(r'<svg\b[\s\S]*?</svg>',lambda m:svg,page,count=1)
if n!=1: raise SystemExit('inline SVG replacement failed')
class_payload=json.dumps(class_data,ensure_ascii=False).replace('</','<\\/')
extra_payload=json.dumps(extra,ensure_ascii=False,separators=(',',':')).replace('</','<\\/')
page,n=re.subn(r'(const CLASS_DATA\s*=\s*)\{.*?\}(;\n)',lambda m:m.group(1)+class_payload+m.group(2),page,count=1,flags=re.S)
if n!=1: raise SystemExit('CLASS_DATA replacement failed')
page,n=re.subn(r'^  let EXTRA_DATA = .*; /\* INJECT_EXTRA_DATA \*/$',lambda m:f'  let EXTRA_DATA = {extra_payload}; /* INJECT_EXTRA_DATA */',page,count=1,flags=re.M)
if n!=1: raise SystemExit('EXTRA_DATA replacement failed')
page=page.replace('<title>NormedField structure hierarchy — Mathlib (July 2026)</title>', '<title>STAGING — unary-closed NormedField structure hierarchy</title>')
page=re.sub(
    r'Mathlib v4\.32\.0-rc1-patch1 · 101 classes, 142 drawn edges \(transitively reduced\) · solid = extends/projection, dashed = derived instance · layout grouped by subject area',
    f'Mathlib v4.32.0 · commit 81a5d257 · {len(NODES)} classes, {len(EDGES)} drawn edges '
    f'({N_SOLID} direct extends + {N_DASHED} dashed) · complete direct unary-instance relation · no transitive reduction · {N_EXCLUDED} Lean.Grind classes excluded',
    page)
page=page.replace('which of 31 standard types', 'which of 32 standard types')
page=page.replace('source (Mathlib v4.32.0-rc1-patch1):', 'source (Mathlib v4.32.0, commit 81a5d257):')
page=page.replace(
    '<code>extends</code> closure from <code>NormedField</code> plus source-verified <code>instance</code> edges, transitively reduced.',
    '<code>extends</code>- and unary-instance-closed staging set, with every direct parent and direct unary arrow retained; classes containing <code>Lean.Grind</code> are intentionally excluded.')
page=page.replace(
    '<body>',
    f'<body>\n<div id="staging-banner" style="position:fixed;z-index:30;left:50%;transform:translateX(-50%);top:8px;background:#8a4b08;color:white;padding:5px 12px;border-radius:999px;font:700 12px system-ui;box-shadow:0 1px 6px #0005;pointer-events:none">STAGING REVIEW · {len(NODES)} nodes · {len(EDGES)} edges · {N_EXCLUDED} Lean.Grind exclusions · production untouched</div>',
    1)
page=page.replace('data: <a href="tooltip_data.json">tooltip_data.json</a>.', 'staging data: <a href="tooltip_data_staging.json">tooltip_data_staging.json</a> and <a href="hierarchy_extras_staging.json">hierarchy_extras_staging.json</a>.')
OUT_HTML.write_text(page)
print(f'wrote {OUT_HTML.name} ({len(NODES)} nodes, {len(EDGES)} edges)')
print(f'embedded {len(class_data)} classes and {len(extra["edges"])} verified edge declarations')
