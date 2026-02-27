#!/usr/bin/env bash
# agda-goals.sh — Load an Agda file and print normalized goal types
#                  and context for all holes.
#
# Usage: ./scripts/agda-goals.sh <file.agda>
#        ./scripts/agda-goals.sh -u <file.agda>   # unnormalized
#
# Requires: agda, python3

set -euo pipefail

NORM="Normalised"
if [[ "${1:-}" == "-u" ]]; then
  NORM="AsIs"
  shift
fi

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 [-u] <file.agda>" >&2
  echo "  -u  Show unnormalized (as-is) goal types" >&2
  exit 1
fi

FILE="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"

if [[ ! -f "$FILE" ]]; then
  echo "Error: file not found: $FILE" >&2
  exit 1
fi

# Step 1: Load the file and collect interaction points
LOAD_OUTPUT=$(echo "IOTCM \"$FILE\" NonInteractive Indirect (Cmd_load \"$FILE\" [])" \
  | agda --interaction-json 2>&1)

# Extract interaction point IDs
GOAL_IDS=$(echo "$LOAD_OUTPUT" \
  | grep '"kind":"InteractionPoints"' \
  | python3 -c "
import sys, json
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    data = json.loads(line)
    for ip in data.get('interactionPoints', []):
        print(ip['id'])
" 2>/dev/null)

if [[ -z "$GOAL_IDS" ]]; then
  # Check for errors
  ERRORS=$(echo "$LOAD_OUTPUT" | grep '"kind":"Error"' || true)
  if [[ -n "$ERRORS" ]]; then
    echo "Agda reported errors:" >&2
    echo "$ERRORS" | python3 -c "
import sys, json
for line in sys.stdin:
    data = json.loads(line.strip())
    info = data.get('info', {})
    err = info.get('error', {})
    msg = err.get('message', '')
    if msg:
        print(msg)
" 2>/dev/null >&2
  else
    echo "No goals found." >&2
  fi
  exit 0
fi

NUM_GOALS=$(echo "$GOAL_IDS" | wc -l | tr -d ' ')
echo "Found $NUM_GOALS goal(s). Querying normalized types..."
echo ""

# Step 2: Build commands — reload + query each goal
# The correct Agda interaction command is Cmd_goal_type_context
# with Normalised/AsIs as the first argument.
CMDS="IOTCM \"$FILE\" NonInteractive Indirect (Cmd_load \"$FILE\" [])"$'\n'
for GID in $GOAL_IDS; do
  CMDS+="IOTCM \"$FILE\" NonInteractive Indirect (Cmd_goal_type_context $NORM $GID noRange \"\")"$'\n'
done

# Step 3: Send all commands and extract GoalSpecific responses
echo "$CMDS" | agda --interaction-json 2>&1 \
  | grep '"kind":"GoalSpecific"' \
  | python3 -c "
import sys, json

goal_num = 0
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    try:
        data = json.loads(line)
    except json.JSONDecodeError:
        continue

    info = data.get('info', {})
    goal_id = info.get('interactionPoint', {}).get('id', '?')

    goal_info = info.get('goalInfo', {})
    goal_type = goal_info.get('type', None)

    # Also check for plain type in info
    if goal_type is None:
        goal_type = info.get('type', '(could not extract type)')

    # Context entries
    entries = goal_info.get('entries', [])

    print(f'━━━ Goal ?{goal_id} ━━━')
    if entries:
        print('Context:')
        for e in entries:
            name = e.get('reifiedName', e.get('name', '?'))
            ty = e.get('type', '?')
            print(f'  {name} : {ty}')
        print()
    print(f'Goal: {goal_type}')
    print()
    goal_num += 1

if goal_num == 0:
    print('No GoalSpecific responses received. The goals may have failed to normalize.')
    print('Try running: agda --no-main <file> to see raw errors.')
" 2>/dev/null
