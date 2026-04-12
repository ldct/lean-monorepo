#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Initialize conda for non-interactive shells.
# Temporarily disable nounset — conda's scripts reference unbound variables.
set +u
eval "$(conda shell.bash hook 2>/dev/null)" || {
    echo "ERROR: conda not found. Please install conda and ensure it is on your PATH."
    exit 1
}
set -u

PYTHON="$(conda run -n agent which python)"

PDF_PATH="${1:?Usage: bash run_pdf_to_latex.sh <input.pdf>}"
OUTPUT_DIR="$SCRIPT_DIR/extracted_latex"

mkdir -p "$OUTPUT_DIR"

echo "=== PDF to LaTeX Conversion ==="
echo "  Input:  $PDF_PATH"
echo "  Output: $OUTPUT_DIR"
echo ""

# Step 1: Convert PDF to LaTeX chapter files
"$PYTHON" "$SCRIPT_DIR/pdf_to_latex/convert.py" "$PDF_PATH" "$OUTPUT_DIR" --split-chapters

# Step 2: Validate output format
echo ""
echo "=== Validating Output Format ==="
"$PYTHON" "$SCRIPT_DIR/pdf_to_latex/validate_format.py" "$OUTPUT_DIR" | tee "$OUTPUT_DIR/validation_report.txt"

echo ""
echo "Validation report saved to: $OUTPUT_DIR/validation_report.txt"
