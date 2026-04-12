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
CONFIG="$SCRIPT_DIR/config.yaml"

DEFAULT_INPUT="$SCRIPT_DIR/extracted_latex"
DEFAULT_OUTPUT="$SCRIPT_DIR/lean_formalization_output"

# If the first arg starts with '-' or no args given, use defaults and pass everything as flags.
# Otherwise, treat first two args as input/output dirs.
if [ $# -eq 0 ] || [[ "$1" == -* ]]; then
    INPUT_DIR="$DEFAULT_INPUT"
    OUTPUT_DIR="$DEFAULT_OUTPUT"
    EXTRA_ARGS=("$@")
else
    INPUT_DIR="$1"
    OUTPUT_DIR="$2"
    shift 2
    EXTRA_ARGS=("$@")
fi

echo "=== Textbook-to-Lean Formalization Pipeline ==="
echo "  Input:  $INPUT_DIR"
echo "  Output: $OUTPUT_DIR"
echo "  Config: $CONFIG"
echo ""

exec "$PYTHON" "$SCRIPT_DIR/code/pipeline.py" \
    --input "$INPUT_DIR" \
    --output "$OUTPUT_DIR" \
    --config "$CONFIG" \
    ${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}
