#!/usr/bin/env python3
"""Compare a regenerated site/tooltip_data.json against a reference copy.

Usage: python3 scripts/compare_tooltip_data.py [new] [ref]
Defaults: new = site/tooltip_data.json, ref = site/tooltip_data.json.ref

Reports: missing/extra/misordered entries, per-entry key-set differences, and
per-path value differences grouped by pattern (with a few examples each).
"""

import json
import sys
from collections import defaultdict

STRUCTURAL_KEYS = {"isAbbrev", "fieldCount", "copiedFromParents", "leanName",
                   "subobject", "projection", "proj", "owner", "kind", "name"}


def walk(path, a, b, diffs):
    if type(a) is not type(b):
        diffs[path].append((a, b))
    elif isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a:
                diffs[f"{path}.{k} (missing in new)"].append((None, b[k]))
            elif k not in b:
                diffs[f"{path}.{k} (extra in new)"].append((a[k], None))
            else:
                walk(f"{path}.{k}", a[k], b[k], diffs)
    elif isinstance(a, list):
        if len(a) != len(b):
            an = [x.get("name") if isinstance(x, dict) else x for x in a]
            bn = [x.get("name") if isinstance(x, dict) else x for x in b]
            diffs[f"{path} (length)"].append((an, bn))
        else:
            for i, (x, y) in enumerate(zip(a, b)):
                tag = x.get("name", i) if isinstance(x, dict) else i
                walk(f"{path}[{tag}]", x, y, diffs)
    elif a != b:
        diffs[path].append((a, b))


def pattern(path):
    """Group e.g. 'Ring.ownFields[zsmul].type' -> 'ownFields[].type'."""
    parts = path.split(".", 1)
    if len(parts) == 1:
        return path
    rest = parts[1]
    out, i = [], 0
    while i < len(rest):
        c = rest[i]
        if c == "[":
            j = rest.index("]", i)
            out.append("[]")
            i = j + 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def main():
    new_path = sys.argv[1] if len(sys.argv) > 1 else "site/tooltip_data.json"
    ref_path = sys.argv[2] if len(sys.argv) > 2 else "site/tooltip_data.json.ref"
    new = json.load(open(new_path))
    ref = json.load(open(ref_path))

    new_by = {e["name"]: e for e in new}
    ref_by = {e["name"]: e for e in ref}
    new_names = [e["name"] for e in new]
    ref_names = [e["name"] for e in ref]

    print(f"entries: new={len(new)} ref={len(ref)}")
    missing = [n for n in ref_names if n not in new_by]
    extra = [n for n in new_names if n not in ref_by]
    if missing:
        print("MISSING in new:", missing)
    if extra:
        print("EXTRA in new:", extra)
    if new_names == ref_names:
        print("entry order: identical")
    else:
        print("entry order: DIFFERS")

    diffs = defaultdict(list)
    for name in ref_names:
        if name in new_by:
            walk(name, new_by[name], ref_by[name], diffs)

    if not diffs:
        print("all entries: deep-equal")
        return

    grouped = defaultdict(list)
    for path, pairs in diffs.items():
        for a, b in pairs:
            grouped[pattern(path)].append((path, a, b))

    structural = 0
    for pat in sorted(grouped):
        items = grouped[pat]
        is_structural = any(k in pat for k in STRUCTURAL_KEYS) and \
            not pat.endswith(".doc") and not pat.endswith(".type")
        if is_structural:
            structural += len(items)
        print(f"\n== {pat}: {len(items)} diffs"
              f"{'  [STRUCTURAL]' if is_structural else ''}")
        for path, a, b in items[:4]:
            print(f"  at {path}")
            print(f"    new: {json.dumps(a, ensure_ascii=False)[:220]}")
            print(f"    ref: {json.dumps(b, ensure_ascii=False)[:220]}")

    print(f"\ntotal value diffs: {sum(len(v) for v in grouped.values())}"
          f" ({structural} structural)")


if __name__ == "__main__":
    main()
