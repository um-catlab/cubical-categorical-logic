#!/usr/bin/env bash
# originally written by Steven Schaefer <stschaef>

error=0
shopt -s globstar nullglob
for file in **/*.agda; do
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
done
exit ${error}
