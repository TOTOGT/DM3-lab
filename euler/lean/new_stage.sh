#!/usr/bin/env bash
# Start the next stage file as a copy of the newest one (each stage is cumulative).
# Usage: euler/lean/new_stage.sh StageA4c     (then append the new section and run stage.sh)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)/euler/lean/EulerLean"
new="${1:?usage: new_stage.sh StageNAME}"
last=$(git log --diff-filter=A --format= --name-only -- 'StageA*.lean' | sed -n '1p' | sed 's#.*/##')
[ -f "$new.lean" ] && { echo "$new.lean exists"; exit 1; }
cp "$last" "$new.lean"
echo "copied $last -> $new.lean"
