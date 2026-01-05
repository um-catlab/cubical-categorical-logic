#!/bin/bash

# Default values
PROFILE_MODE=false

# Parse flags
while [[ $# -gt 0 ]]; do
    case $1 in
        -p|--profile)
            PROFILE_MODE=true
            shift
            ;;
        *)
            break
            ;;
    esac
done

# Check if file argument is provided
if [ $# -lt 1 ]; then
    echo "Usage: $0 [-p|--profile] <agda-file> [<tc.decl> <tc.constr.add> <tc.pos>]"
    echo ""
    echo "Options:"
    echo "  -p, --profile    Enable profiling mode (disables verbose output)"
    echo ""
    echo "Example (normal mode):  $0 Cubical/Categories/Displayed/Constructions/Reindex/Cartesian.agda 50 50 30"
    echo "Example (profile mode): $0 -p Cubical/Categories/Displayed/Constructions/Reindex/Cartesian.agda"
    exit 1
fi

AGDA_FILE="$1"

if [ "$PROFILE_MODE" = false ]; then
    # Normal mode requires verbosity arguments
    if [ $# -lt 4 ]; then
        echo "Error: Normal mode requires verbosity arguments"
        echo "Usage: $0 <agda-file> <tc.decl> <tc.constr.add> <tc.pos>"
        exit 1
    fi
    TC_DECL="$2"
    TC_CONSTR_ADD="$3"
    TC_POS="$4"
fi

# Check if file exists
if [ ! -f "$AGDA_FILE" ]; then
    echo "Error: File '$AGDA_FILE' not found"
    exit 1
fi

# Generate timestamp
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")

# Find git root (project root), fallback to current directory
PROJECT_ROOT=$(git rev-parse --show-toplevel 2>/dev/null || pwd)

# Clear Agda cache for this specific file
echo "Clearing Agda cache for: $AGDA_FILE"

# Get the .agdai filename (replace .agda with .agdai)
AGDAI_FILE="${AGDA_FILE%.agda}.agdai"

# Remove .agdai file in the same directory as source
if [ -f "$AGDAI_FILE" ]; then
    rm "$AGDAI_FILE"
    echo "Removed: $AGDAI_FILE"
fi

# Remove .agdai file in _build directory (typical location)
if [ -d "$PROJECT_ROOT/_build" ]; then
    # Find and remove all .agdai files matching this source file in _build
    find "$PROJECT_ROOT/_build" -type f -path "*/${AGDAI_FILE}" -delete 2>/dev/null
    echo "Removed .agdai files from _build directory"
fi

echo ""

# Get directory structure and filename
FILE_DIR=$(dirname "$AGDA_FILE")
FILE_NAME=$(basename "$AGDA_FILE")

# Create output directory mirroring the path structure
OUTPUT_DIR="$PROJECT_ROOT/output/$FILE_DIR"
mkdir -p "$OUTPUT_DIR"

echo "Running agda on: $AGDA_FILE"

if [ "$PROFILE_MODE" = true ]; then
    PROF_FILE="$OUTPUT_DIR/${FILE_NAME}_${TIMESTAMP}.prof"

    echo "Mode: Profiling enabled"
    echo "Profiling data will be saved to: $PROF_FILE"
    echo ""

    # Remove old agda.prof if it exists
    rm -f agda.prof

    # Run agda with profiling (using -pj for JSON output)
    time agda +RTS -pj -RTS "$AGDA_FILE"

    # Move the profiling output to the output directory
    if [ -f "agda.prof" ]; then
        mv agda.prof "$PROF_FILE"
        echo ""
        echo "Profiling complete! Results saved to: $PROF_FILE"
    else
        echo ""
        echo "Warning: agda.prof was not generated"
    fi
else
    OUTPUT_FILE="$OUTPUT_DIR/${FILE_NAME}_${TC_DECL}_${TC_CONSTR_ADD}_${TC_POS}_${TIMESTAMP}.txt"

    echo "Verbosity: tc.decl:$TC_DECL tc.constr.add:$TC_CONSTR_ADD tc.pos:$TC_POS"
    echo "Output will be saved to: $OUTPUT_FILE"
    echo ""
    time agda -vtc.decl:$TC_DECL -vtc.constr.add:$TC_CONSTR_ADD -vtc.pos:$TC_POS "$AGDA_FILE" | tee "$OUTPUT_FILE"
fi
