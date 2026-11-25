#!/usr/bin/env python3
"""Euler Lean proof-agent supervisor (integration lane).

Never pushes, never runs `git add -A`. Reads drafts/*.status.md, promotes drafts whose first line is
'STATE: ready-for-CI' to numbered modules EDc<N>.lean plus a workflow that compiles the chain with
GitHub CI and parses declaration-specific axiom reports (agents/check_axioms.py). Writes state.json.
Usage: supervisor.py status | promote [name ...]
"""
import json, re, sys, hashlib, shutil, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
ED = ROOT / "euler/lean/EulerLean/ED"
DR = ED / "drafts"
WF = ROOT / ".github/workflows"
ST = Path(__file__).resolve().parent / "state.json"
BASE = ("StageA4o Stage83cut EDa1 EDa6 EDa7 EDa8 EDa9 EDb1 EDb2 EDb3 EDb4 EDb5 EDb6 EDb7 EDb8 "
        "EDc0 EDcDefs EDc1 EDc2 EDc4")
# per-draft: extra modules before the new one
EXTRA = {"splitting_transport": "EDc7", "weil_fibre": "EDc6", "vertex_quotient": "", "edge_count": ""}

def state():
    return json.loads(ST.read_text()) if ST.exists() else {"promoted": {}, "next": 8, "log": []}

def draft_state(n):
    p = DR / f"{n}.status.md"
    return p.read_text().splitlines()[0].strip() if p.exists() else "STATE: missing"

def gates(src):
    return re.findall(r"^#print axioms\s+(\S+)", src, re.M)

def forbidden(src):
    bad = []
    for pat, why in [(r"\bsorry\b", "sorry"), (r"^\s*axiom\b", "axiom declaration"),
                     (r":\s*True\s*:=", "vacuous True statement"), (r"\bRPEigen\b.*:=\s*by\s+trivial", "trivial RPEigen")]:
        if re.search(pat, re.sub(r"/-.*?-/", "", src, flags=re.S), re.M):
            bad.append(why)
    return bad

WF_T = """# {mod}: promoted from drafts/{name}. UNTESTED until this run is green. Does NOT prove RPEigen.
name: Euler {mod} (Lean)
on:
  workflow_dispatch:
  push:
    paths:
      - 'euler/lean/EulerLean/ED/{mod}.lean'
      - '.github/workflows/euler-{low}.yml'
      - 'euler/lean/agents/check_axioms.py'
jobs:
  {low}:
    runs-on: ubuntu-latest
    defaults:
      run:
        working-directory: euler/lean
    timeout-minutes: 240
    steps:
      - uses: actions/checkout@v4
      - name: Install elan
        run: |
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- --default-toolchain none -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
      - name: Fetch Mathlib cache
        run: |
          set -euxo pipefail
          lake update
          lake exe cache get || echo "::warning::cache get failed; Mathlib will build from source"
      - name: Assert pins
        run: |
          set -uxo pipefail
          lake env lean --version | tee /tmp/ver.txt
          grep -q 'version 4.32.0' /tmp/ver.txt || {{ echo "::error::Lean is not 4.32.0"; exit 1; }}
          rev=$(git -C .lake/packages/mathlib rev-parse HEAD)
          [ "$rev" = "81a5d257c8e410db227a6665ed08f64fea08e997" ] || {{ echo "::error::Mathlib rev mismatch"; exit 1; }}
      - name: Compile chain and gate
        run: |
          set -uxo pipefail
          W=$GITHUB_WORKSPACE/ci_{low}
          mkdir -p $W
          MODS="{mods}"
          cp EulerLean/StageA4o.lean $W/
          for m in $MODS; do [ "$m" = StageA4o ] || cp EulerLean/ED/$m.lean $W/ 2>/dev/null || cp EulerLean/$m.lean $W/; done
          export LEAN_PATH="$(lake env printenv LEAN_PATH):$W"
          for m in $MODS; do
            echo "::group::$m"
            lean -R $W -o $W/$m.olean $W/$m.lean 2>&1 | tee $W/$m.out
            rc=${{PIPESTATUS[0]}}
            echo "::endgroup::"
            [ "$rc" -eq 0 ] || {{ echo "::error::$m exited $rc"; exit 1; }}
            if grep -nE ": error" $W/$m.out; then echo "::error::error in $m"; exit 1; fi
          done
          if grep -nE "(^|[^a-zA-Z_])sorry" $W/{mod}.out; then echo "::error::sorry in {mod}"; exit 1; fi
          python3 $GITHUB_WORKSPACE/euler/lean/agents/check_axioms.py $W/{mod}.out {gates} | tee -a $GITHUB_STEP_SUMMARY
"""

def promote(name, s):
    if draft_state(name) != "STATE: ready-for-CI":
        return f"{name}: not ready ({draft_state(name)})"
    src = (DR / f"{name}.lean").read_text()
    bad = forbidden(src)
    if bad:
        return f"{name}: REJECTED ({', '.join(bad)})"
    g = gates(src)
    if not g:
        return f"{name}: REJECTED (no #print axioms gates)"
    n = s["next"]; mod = f"EDc{n}"
    (ED / f"{mod}.lean").write_text(src)
    assert hashlib.sha256((ED / f"{mod}.lean").read_bytes()).hexdigest() == hashlib.sha256(src.encode()).hexdigest()
    mods = f"{BASE} {EXTRA.get(name,'')} {mod}".split()
    mods = " ".join(m for m in mods if m)
    (WF / f"euler-{mod.lower()}.yml").write_text(WF_T.format(mod=mod, low=mod.lower(), name=name, mods=mods, gates=" ".join(g)))
    s["promoted"][name] = {"module": mod, "gates": g, "sha256": hashlib.sha256(src.encode()).hexdigest()[:16], "time": time.strftime("%FT%TZ", time.gmtime())}
    s["next"] = n + 1
    (DR / f"{name}.status.md").write_text(f"STATE: promoted({mod})\n" + "\n".join((DR / f"{name}.status.md").read_text().splitlines()[1:]) + "\n")
    return f"{name}: promoted as {mod} with {len(g)} axiom gates"

if __name__ == "__main__":
    s = state(); cmd = sys.argv[1] if len(sys.argv) > 1 else "status"
    names = sys.argv[2:] or list(EXTRA)
    if cmd == "promote":
        for n in names:
            if n not in s["promoted"]:
                r = promote(n, s); print(r); s["log"].append(r)
    else:
        for n in EXTRA:
            print(n, draft_state(n), s["promoted"].get(n, ""))
    ST.write_text(json.dumps(s, indent=1))
