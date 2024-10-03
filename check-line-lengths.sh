#!/usr/bin/env bash
# originally written by Steven Schaefer <stschaef>

error=0

VENV_DIR="env"

# Check if the virtual environment directory exists
if [ ! -d "$VENV_DIR" ]; then
    echo "Virtual environment does not exist. Creating one now..."
    # Create the virtual environment with python3
    python3 -m venv "$VENV_DIR" || { echo "Failed to create virtual environment."; exit 1; }

fi

if [ ! -e "$VENV_DIR/bin/activate" ]; then
    echo "If you just installed python3-venv, you need to remove $VENV_DIR and re-run this script"
    exit 1
fi
source "$VENV_DIR/bin/activate"

if [ $? -ne 0 ]; then
    echo "Error: Unable to activate the virtual environment."
    exit 2
fi

echo "Virtual environment activated."

pip3 install wcwidth || { echo "Failed to install wcwidth."; exit 3; }

echo "Package 'wcwidth' has been successfully installed in the virtual environment."

while IFS= read -r -d '' file; do
  python3 -c '
import sys
from wcwidth import wcswidth
filename = sys.argv[1]
try:
    with open(filename, "r", encoding="utf-8") as file:
        for lineno, line in enumerate(file, 1):
            if wcswidth(line.rstrip("\n")) > 80:
                print(f"{filename}:{lineno}: line too long")
                sys.exit(1)
except Exception as e:
    print(f"Error processing {filename}: {e}")
    sys.exit(1)
  ' "${file}" || error=1
done  < <(find . -name '*.agda' -print0)
exit ${error}
