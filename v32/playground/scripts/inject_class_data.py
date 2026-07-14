#!/usr/bin/env python3
"""Inline site/tooltip_data.json into normedfield_hierarchy.html as CLASS_DATA.

tooltip_data.json is an array of per-class entries (see
scripts/extract_tooltip_data.lean); CLASS_DATA in the HTML is the same data
keyed by entry name. Rerunnable: replaces the whole `const CLASS_DATA = {...};`
blob (same regex as scripts/fix_added_over_parents.py).

Run after scripts/extract_tooltip_data.lean and BEFORE
scripts/fix_added_over_parents.py (which post-processes both copies).
"""
import json
import pathlib
import re
import sys

site = pathlib.Path(__file__).resolve().parent.parent / "site"
entries = json.loads((site / "tooltip_data.json").read_text())
by_name = {e["name"]: e for e in entries}
if len(by_name) != len(entries):
    sys.exit("duplicate names in tooltip_data.json")
payload = json.dumps(by_name, ensure_ascii=False)
payload = payload.replace("</", "<\\/")  # never close the <script> tag

html_path = site / "normedfield_hierarchy.html"
html = html_path.read_text()
m = re.search(r"(const CLASS_DATA\s*=\s*)(\{.*?\})(;\n)", html, re.S)
if not m:
    sys.exit("CLASS_DATA not found in HTML")
html = html[: m.start(2)] + payload + html[m.end(2):]
html_path.write_text(html)
print(f"injected {len(by_name)} classes ({len(payload)} bytes) into {html_path.name}")
