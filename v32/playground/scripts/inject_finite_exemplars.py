#!/usr/bin/env python3
"""Inline site/finite_exemplars.json into normedfield_hierarchy.html.

Rerunnable: replaces the `let FINITE_EX = ...; /* INJECT_FINITE_EX */` line,
inserting it right after the `const EX = EXTRA_DATA ...` line if not present yet.
Run after (re)generating the data with scripts/gen_finite_exemplars.py.
"""
import json
import pathlib
import re

site = pathlib.Path(__file__).resolve().parent.parent / "site"
html_path = site / "normedfield_hierarchy.html"
data = json.load(open(site / "finite_exemplars.json"))
payload = json.dumps(data, ensure_ascii=False, separators=(",", ":"))
payload = payload.replace("</", "<\\/")  # never close the <script> tag

html = html_path.read_text()
new_line = f"  let FINITE_EX = {payload}; /* INJECT_FINITE_EX */"

if "/* INJECT_FINITE_EX */" in html:
    html2, n = re.subn(r"^  let FINITE_EX = .*; /\* INJECT_FINITE_EX \*/$",
                       lambda m: new_line, html, count=1, flags=re.M)
    assert n == 1, "INJECT_FINITE_EX marker found but not replaceable"
else:
    anchor = re.compile(r"^(  const EX = EXTRA_DATA \|\|.*;)$", flags=re.M)
    html2, n = anchor.subn(lambda m: m.group(1) + "\n" + new_line, html, count=1)
    assert n == 1, "anchor `const EX = EXTRA_DATA ...` not found"

html_path.write_text(html2)
print(f"injected {len(payload)} bytes ({len(data)} exemplars) into {html_path.name}")
