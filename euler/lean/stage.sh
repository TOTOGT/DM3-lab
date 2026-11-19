#!/usr/bin/env bash
# One command for the whole loop: commit, push, wait for the "Euler layer A (latest stage)" run, print the result.
# Usage (from anywhere inside the DM3-lab clone):  euler/lean/stage.sh "Euler layer A: StageA4b (T_m self-adjoint)"
# No gh needed. Reads the public GitHub API, so it can show steps and conclusions but not log text:
# open the printed run URL for the job summary (axiom table) or the failing step's log.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
msg="${1:?usage: stage.sh \"commit message\"}"
repo="TOTOGT/DM3-lab"
wf="euler-layerA-latest.yml"

git add euler/lean .github/workflows
git commit -m "$msg" || echo "(nothing new to commit)"
git pull --rebase --autostash
git push
sha=$(git rev-parse HEAD)
echo "pushed $sha"

api() { curl -fsS "https://api.github.com/repos/$repo/$1"; }
pyget() { python3 -c "import sys,json;d=json.load(sys.stdin);$1"; }

id=""
for _ in $(seq 1 30); do
  id=$(api "actions/workflows/$wf/runs?head_sha=$sha&per_page=1" | pyget 'r=d.get("workflow_runs",[]);print(r[0]["id"] if r else "")' || true)
  [ -n "$id" ] && break
  sleep 10
done
if [ -z "$id" ]; then
  echo "No run appeared for $sha. The workflow starts only when a StageA*.lean file changes in the push."
  echo "Start it by hand: https://github.com/$repo/actions/workflows/$wf"
  exit 1
fi
echo "run $id: https://github.com/$repo/actions/runs/$id"

while :; do
  st=$(api "actions/runs/$id" | pyget 'print(d["status"],d.get("conclusion") or "-")')
  set -- $st
  printf '%s  %s\n' "$(date +%H:%M:%S)" "$1 $2"
  [ "$1" = "completed" ] && break
  sleep 30
done

api "actions/runs/$id/jobs" | pyget '
for j in d["jobs"]:
    for s in j["steps"]:
        print("  %2d  %-28s %s" % (s["number"], s["name"], s["conclusion"]))'
[ "$2" = "success" ] && { echo "PASS"; exit 0; }
echo "FAIL ($2): open the run URL above and paste me the failing step's output."
exit 1
