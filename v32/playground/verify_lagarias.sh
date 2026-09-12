#!/usr/bin/env bash
# Usage: bash verify_lagarias.sh [--helpers | --target | --complete]
# --helpers (default): build and audit every helper module.
# --target: audit the actual RH equivalence; this FAILS while its sorry remains.
# --complete: require both checks. A successful ordinary lake build is not enough.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

mode=${1:---helpers}
if (($# > 1)) || [[ "$mode" != --helpers && "$mode" != --target && "$mode" != --complete ]]; then
  echo 'Usage: bash verify_lagarias.sh [--helpers | --target | --complete]' >&2
  exit 2
fi

temporary_files=()
cleanup() {
  if ((${#temporary_files[@]})); then
    rm -f -- "${temporary_files[@]}"
  fi
}
trap cleanup EXIT

if [[ "$mode" != --target ]]; then
  mapfile -t modules < <(
    find Playground/Lagarias -type f -name '*.lean' ! -name 'Audit.lean' \
      | LC_ALL=C sort | sed 's#/#.#g; s/\.lean$//'
  )
  if ((${#modules[@]} == 0)); then
    echo 'No Lagarias helper modules found' >&2
    exit 1
  fi
  lake build "${modules[@]}"

  # Import every helper before auditing the namespace. Newly added modules
  # cannot escape the audit through an incomplete hand-maintained import list.
  audit_file=$(mktemp ./LagariasAuditAll_XXXXXX.lean)
  temporary_files+=("$audit_file")
  for module in "${modules[@]}"; do
    printf 'import %s\n' "$module" >> "$audit_file"
  done
  cat Playground/Lagarias/Audit.lean >> "$audit_file"
  lake env lean "$audit_file"
fi

if [[ "$mode" != --helpers ]]; then
  target_file=$(mktemp ./LagariasAuditTarget_XXXXXX.lean)
  temporary_files+=("$target_file")
  printf 'import Lean.Util.CollectAxioms\n' >> "$target_file"
  cat ../Lagarias.lean >> "$target_file"
  cat >> "$target_file" <<'LEAN'

-- Check the criterion's actual definition, not merely its name.
example : LeanEval.NumberTheory.LagariasElementaryCriterion =
    (∀ n : ℕ, 0 < n →
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
        (harmonic n : ℝ) +
          Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) := rfl

-- Check that the unchanged theorem really has the requested type.
example : RiemannHypothesis ↔ LeanEval.NumberTheory.LagariasElementaryCriterion :=
  LeanEval.NumberTheory.riemann_hypothesis_iff_lagarias_elementary_criterion

open Lean Elab Command in
run_cmd do
  let target := ``LeanEval.NumberTheory.riemann_hypothesis_iff_lagarias_elementary_criterion
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms target
  let forbidden := axioms.filter fun axiomName => !allowed.contains axiomName
  unless forbidden.isEmpty do
    throwError "INCOMPLETE: the original Lagarias equivalence depends on {forbidden}"
  logInfo "COMPLETE: the original Lagarias equivalence uses only standard axioms."
LEAN
  lake env lean "$target_file"
fi
