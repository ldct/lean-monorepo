#!/usr/bin/env bash
# Compile-check every finite-exemplar snippet as a standalone Lean file
# (mirroring the live.lean-lang.org context: `import Mathlib` + the snippet).
set -u
cd "$(dirname "$0")/.."
TMP=$(mktemp -d)
python3 - "$TMP" <<'PY'
import json, sys, os
tmp = sys.argv[1]
d = json.load(open("site/finite_exemplars.json"))
for node, v in d.items():
    open(os.path.join(tmp, f"{node}.lean"), "w").write(v["code"])
print("\n".join(d.keys()))
PY
fail=0
# compile in batches of 4 to bound memory
nodes=$(python3 -c "import json;print(' '.join(json.load(open('site/finite_exemplars.json')).keys()))")
pids=(); names=()
run() { lake env lean "$TMP/$1.lean" >"$TMP/$1.log" 2>&1; echo $? >"$TMP/$1.rc"; }
i=0
for n in $nodes; do
  run "$n" & pids+=($!); names+=("$n"); i=$((i+1))
  if (( i % 4 == 0 )); then wait; fi
done
wait
for n in $nodes; do
  rc=$(cat "$TMP/$n.rc")
  if [ "$rc" = "0" ]; then echo "PASS  $n"; else echo "FAIL  $n"; sed 's/^/    /' "$TMP/$n.log" | head -12; fail=1; fi
done
rm -rf "$TMP"
exit $fail
