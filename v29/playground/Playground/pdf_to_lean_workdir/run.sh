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

PDF_PATH="${1:?Usage: bash run.sh <input.pdf>}"
EXTRACTED_LATEX_DIR="$SCRIPT_DIR/extracted_latex"
OUTPUT_DIR="$SCRIPT_DIR/lean_formalization_output"
CONFIG="$SCRIPT_DIR/config.yaml"

echo "============================================================"
echo "  Full Pipeline: PDF → LaTeX → Lean Formalization"
echo "============================================================"
echo "  Input PDF:        $PDF_PATH"
echo "  Extracted LaTeX:  $EXTRACTED_LATEX_DIR"
echo "  Lean output:      $OUTPUT_DIR"
echo ""

# Check if extracted_latex already has ch*.txt files
EXISTING_FILES=$(find "$EXTRACTED_LATEX_DIR" -maxdepth 1 -name 'ch*.txt' 2>/dev/null | head -1 || true)
if [ -n "$EXISTING_FILES" ]; then
    echo "============================================================"
    echo "  SKIPPING Steps 1-2: extracted_latex/ is non-empty"
    echo "  Using existing LaTeX files in $EXTRACTED_LATEX_DIR"
    echo "============================================================"
    echo ""
else
    # Step 1: PDF to LaTeX
    echo "============================================================"
    echo "  STEP 1: PDF → LaTeX Conversion"
    echo "============================================================"
    bash "$SCRIPT_DIR/run_pdf_to_latex.sh" "$PDF_PATH"

    # Step 2: Validate LaTeX format
    echo ""
    echo "============================================================"
    echo "  STEP 2: Checking validation report"
    echo "============================================================"
    if ! "$PYTHON" "$SCRIPT_DIR/pdf_to_latex/validate_format.py" "$EXTRACTED_LATEX_DIR"; then
        echo ""
        echo "ERROR: LaTeX validation failed. Fix issues in $EXTRACTED_LATEX_DIR before proceeding."
        echo "See: $EXTRACTED_LATEX_DIR/validation_report.txt"
        exit 1
    fi
    echo "Validation PASSED."
fi

# Step 3: Formalization
echo ""
echo "============================================================"
echo "  STEP 3: LaTeX → Lean Formalization"
echo "============================================================"
"$PYTHON" "$SCRIPT_DIR/code/pipeline.py" \
    --input "$EXTRACTED_LATEX_DIR" \
    --output "$OUTPUT_DIR" \
    --config "$CONFIG" \
    "${@:2}"

echo ""
echo "============================================================"
echo "  PIPELINE COMPLETE"
echo "============================================================"
echo "  Lean project at: $OUTPUT_DIR"
