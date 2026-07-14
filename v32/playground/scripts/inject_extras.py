#!/usr/bin/env python3
"""Inline site/hierarchy_extras.json into normedfield_hierarchy.html.

Rerunnable: replaces the whole `let EXTRA_DATA = ...; /* INJECT_EXTRA_DATA */` line.
Run after (re)generating the data with scripts/extract_hierarchy_extras.lean.
"""
import json
import pathlib
import re

site = pathlib.Path(__file__).resolve().parent.parent / "site"
html_path = site / "normedfield_hierarchy.html"
data = json.load(open(site / "hierarchy_extras.json"))
payload = json.dumps(data, ensure_ascii=False, separators=(",", ":"))
payload = payload.replace("</", "<\\/")  # never close the <script> tag

html = html_path.read_text()
new_line = f"  let EXTRA_DATA = {payload}; /* INJECT_EXTRA_DATA */"
html2, n = re.subn(r"^  let EXTRA_DATA = .*; /\* INJECT_EXTRA_DATA \*/$",
                   lambda m: new_line, html, count=1, flags=re.M)
assert n == 1, "INJECT_EXTRA_DATA marker not found (or found twice)"
html_path.write_text(html2)
print(f"injected {len(payload)} bytes into {html_path.name}")
