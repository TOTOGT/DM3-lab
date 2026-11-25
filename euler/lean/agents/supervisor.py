#!/usr/bin/env python3
"""Euler Lean proof-agent supervisor (integration lane).

Never pushes, never runs `git add -A`. Reads drafts/*.status.md, promotes drafts whose first line is
'STATE: ready-for-CI' to numbered modules EDc<N>.lean plus a workflow that compiles the chain with
GitHub CI and parses declaration-specific axiom reports (agents/check_axioms.py). Writes state.json.
Usage: supervisor.py status | promote [name ...]
"""
import json, re, sys, hashlib, shutil, time
from pathlib import Path
from build_cached import make_plan

ROOT = Path(__file__).resolve().parents[3]
ED = ROOT / "euler/lean/EulerLean/ED"
DR = ED / "drafts"
WF = ROOT / ".github/workflows"
ST = Path(__file__).resolve().parent / "state.json"
LANES = ("splitting_transport", "weil_fibre", "vertex_quotient", "edge_count")

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

def workflow_text(mod, declarations):
    paths = [Path(item["source"]).relative_to(ROOT).as_posix()
             for item in make_plan(ROOT / "euler/lean", mod)["modules"]]
    paths.extend(["euler/lean/lean-toolchain", "euler/lean/lake-manifest.json",
                  "euler/lean/lakefile.toml", "euler/lean/agents/build_cached.py",
                  "euler/lean/agents/check_axioms.py", ".github/workflows/euler-proof-cache.yml",
                  f".github/workflows/euler-{mod.lower()}.yml"])
    filters = "\n".join(f"      - {path}" for path in paths)
    return f"""name: Euler {mod} (Lean)
on:
  workflow_dispatch:
  push:
    paths:
{filters}
permissions:
  contents: read
jobs:
  {mod.lower()}:
    uses: ./.github/workflows/euler-proof-cache.yml
    with:
      targets: {mod} {' '.join(declarations)}
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
    (WF / f"euler-{mod.lower()}.yml").write_text(workflow_text(mod, g))
    s["promoted"][name] = {"module": mod, "gates": g, "sha256": hashlib.sha256(src.encode()).hexdigest()[:16], "time": time.strftime("%FT%TZ", time.gmtime())}
    s["next"] = n + 1
    (DR / f"{name}.status.md").write_text(f"STATE: promoted({mod})\n" + "\n".join((DR / f"{name}.status.md").read_text().splitlines()[1:]) + "\n")
    return f"{name}: promoted as {mod} with {len(g)} axiom gates"

if __name__ == "__main__":
    s = state(); cmd = sys.argv[1] if len(sys.argv) > 1 else "status"
    names = sys.argv[2:] or list(LANES)
    if cmd == "promote":
        for n in names:
            if n not in s["promoted"]:
                r = promote(n, s); print(r); s["log"].append(r)
    else:
        for n in LANES:
            print(n, draft_state(n), s["promoted"].get(n, ""))
    ST.write_text(json.dumps(s, indent=1))
