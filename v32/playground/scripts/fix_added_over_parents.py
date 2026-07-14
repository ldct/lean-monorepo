#!/usr/bin/env python3
"""Fix addedOverParents in the NormedField hierarchy tooltip data.

The original generator computed a class's "added over parents" fields as its
literal constructor fields minus subobject parents. But when declared parents
overlap (e.g. Ring extends Semiring, AddCommGroup, AddGroupWithOne), Lean
cannot embed the overlapping parents as subobjects and instead copies their
missing fields into the child's constructor. Those copies (e.g. Ring.zsmul)
are provided by declared parents and are not new requirements.

This script recomputes addedOverParents = ownFields minus the union of the
direct parents' flattened field names, and records the dropped names under
copiedFromParents. It rewrites both site/tooltip_data.json and the CLASS_DATA
blob embedded in site/normedfield_hierarchy.html.

Sanity check: the flattened field-name sets reconstructed here match the
recorded fieldCount for every class.
"""

import json
import re
import sys
from functools import lru_cache
from pathlib import Path

SITE = Path(__file__).resolve().parent.parent / "site"


def fix_entries(entries):
    by_name = {e["name"]: e for e in entries}

    @lru_cache(None)
    def flat(name):
        e = by_name[name]
        s = {f["name"] for f in e.get("ownFields", [])}
        for p in e.get("parents", []):
            s |= flat(p["name"])
        return frozenset(s)

    for e in entries:
        want = e.get("fieldCount")
        if want is not None and len(flat(e["name"])) != want:
            sys.exit(f"fieldCount mismatch for {e['name']}: "
                     f"computed {len(flat(e['name']))}, recorded {want}")

    changed = []
    for e in entries:
        parent_fields = set()
        for p in e.get("parents", []):
            parent_fields |= flat(p["name"])
        added = e.get("addedOverParents", [])
        kept = [f for f in added if f["name"] not in parent_fields]
        copied = [f["name"] for f in added if f["name"] in parent_fields]
        if copied:
            e["addedOverParents"] = kept
            e["copiedFromParents"] = copied
            changed.append((e["name"], copied))
    return changed


def main():
    json_path = SITE / "tooltip_data.json"
    entries = json.loads(json_path.read_text())
    changed = fix_entries(entries)
    json_path.write_text(json.dumps(entries, ensure_ascii=False))

    html_path = SITE / "normedfield_hierarchy.html"
    html = html_path.read_text()
    m = re.search(r"(const CLASS_DATA\s*=\s*)(\{.*?\})(;\n)", html, re.S)
    if not m:
        sys.exit("CLASS_DATA not found in HTML")
    class_data = json.loads(m.group(2))
    fix_entries(list(class_data.values()))
    html = (html[: m.start(2)]
            + json.dumps(class_data, ensure_ascii=False)
            + html[m.end(2):])
    html_path.write_text(html)

    for name, copied in changed:
        print(f"{name}: moved to copiedFromParents: {', '.join(copied)}")
    print(f"{len(changed)} classes fixed")


if __name__ == "__main__":
    main()
