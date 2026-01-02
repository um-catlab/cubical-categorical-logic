#!/bin/bash

# Check if file argument is provided
if [ $# -lt 4 ]; then
    echo "Usage: $0 <agda-file> <tc.decl> <tc.constr.add> <tc.pos>"
    echo "Example: $0 Cubical/Categories/Displayed/Constructions/Reindex/Cartesian.agda 50 50 30"
    exit 1
fi

AGDA_FILE="$1"
TC_DECL="$2"
TC_CONSTR_ADD="$3"
TC_POS="$4"
TC_OPQ="$5"

# Check if file exists
if [ ! -f "$AGDA_FILE" ]; then
    echo "Error: File '$AGDA_FILE' not found"
    exit 1
fi

# Find git root (project root), fallback to current directory
PROJECT_ROOT=$(git rev-parse --show-toplevel 2>/dev/null || pwd)

# Get directory structure and filename
FILE_DIR=$(dirname "$AGDA_FILE")
FILE_NAME=$(basename "$AGDA_FILE")

# Create output directory mirroring the path structure
OUTPUT_DIR="$PROJECT_ROOT/output/$FILE_DIR"
mkdir -p "$OUTPUT_DIR"

# Create output filename with verbosity levels
OUTPUT_FILE="$OUTPUT_DIR/${FILE_NAME}_${TC_DECL}_${TC_CONSTR_ADD}_${TC_POS}_${TC_OPQ}.txt"

echo "Running agda on: $AGDA_FILE"
echo "Verbosity: tc.decl:$TC_DECL tc.constr.add:$TC_CONSTR_ADD tc.pos:$TC_POS tc.opaque:$TC_OPQ"
echo "Output will be saved to: $OUTPUT_FILE"
echo ""

time agda -vtc.decl:$TC_DECL -vtc.constr.add:$TC_CONSTR_ADD -vtc.pos:$TC_POS -vtc.opaque:$TC_OPQ "$AGDA_FILE" | tee "$OUTPUT_FILE"
