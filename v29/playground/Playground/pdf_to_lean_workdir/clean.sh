#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "This will delete:"
echo "  $SCRIPT_DIR/lean_formalization_output/"
echo "  $SCRIPT_DIR/extracted_latex/"
echo ""
read -p "Are you sure? [y/N] " confirm
if [[ "$confirm" != [yY] ]]; then
    echo "Aborted."
    exit 0
fi

rm -rf "$SCRIPT_DIR/lean_formalization_output"
rm -rf "$SCRIPT_DIR/extracted_latex"

echo "Cleaned."
