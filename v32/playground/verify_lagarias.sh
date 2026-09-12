#!/usr/bin/env bash
# Run from v32/playground. This deliberately excludes the unfinished RH target.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

mapfile -t modules < <(
  find Playground/Lagarias -type f -name '*.lean' ! -name 'Audit.lean' \
    | LC_ALL=C sort | sed 's#/#.#g; s/\.lean$//'
)
if ((${#modules[@]} == 0)); then
  echo 'No Lagarias helper modules found' >&2
  exit 1
fi
lake build "${modules[@]}"

# Reuse the checked audit implementation, but import every helper first. New
# modules cannot accidentally escape the transitive axiom audit by not being
# listed in a hand-maintained root import file.
audit_file=$(mktemp ./LagariasAuditAll_XXXXXX.lean)
trap 'rm -f "$audit_file"' EXIT
for module in "${modules[@]}"; do
  printf 'import %s\n' "$module" >> "$audit_file"
done
cat Playground/Lagarias/Audit.lean >> "$audit_file"
lake env lean "$audit_file"
