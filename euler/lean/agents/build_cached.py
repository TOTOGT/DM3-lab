#!/usr/bin/env python3
"""Build bare Euler modules with a dependency-sensitive local cache.

Run from anywhere: build_cached.py --project euler/lean --target EDc11
Use --plan-only without Lean installed. This is a compiler runner, not an axiom
gate: run check_axioms.py on the returned target_log after successful compilation.
No package update, workflow dispatch, promotion or git write is performed.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

FORMAT = "euler-lean-cache-v1"
EXTERNAL = {"Mathlib", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible"}


def uncomment(text: str) -> str:
    """Remove nested Lean comments, preserving lines and quoted strings."""
    out, depth, quoted, i = [], 0, False, 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-": depth += 1; i += 2
            elif pair == "-/": depth -= 1; i += 2
            else:
                if text[i] == "\n": out.append("\n")
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                i += 1; out.append(text[i])
            elif text[i] == '"': quoted = False
            i += 1
        elif pair == "/-": depth = 1; out.append(" "); i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            if text[i] == '"': quoted = True
            out.append(text[i]); i += 1
    if depth: raise ValueError("unterminated Lean block comment")
    return "".join(out)


def make_plan(project: Path, target: str) -> dict:
    project = project.resolve()
    sources = {}
    for directory in (project / "EulerLean", project / "EulerLean/ED"):
        for path in directory.glob("*.lean"):
            if path.stem in sources: raise ValueError(f"ambiguous module: {path.stem}")
            sources[path.stem] = path
    pins = {name: (project / name).read_bytes().hex()
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}
    order, active, records = [], set(), {}

    def visit(name):
        if name in active: raise ValueError(f"cyclic import: {name}")
        if name in records: return
        if name not in sources: raise ValueError(f"missing local module: {name}")
        active.add(name)
        path = sources[name]
        body = path.read_bytes()
        deps = []
        for line in uncomment(body.decode()).splitlines():
            match = re.match(r"^\s*(?:public\s+|private\s+)?import\s+(.+)$", line)
            if not match: continue
            for dependency in match[1].split():
                if dependency in sources:
                    visit(dependency)
                    if dependency not in deps: deps.append(dependency)
                elif dependency.split(".")[0] not in EXTERNAL:
                    raise ValueError(f"unresolved import {dependency} in {name}")
        payload = {"format": FORMAT, "pins": pins,
                   "source_sha256": hashlib.sha256(body).hexdigest(),
                   "imports": {d: records[d]["key"] for d in deps},
                   "compiler_flags": ["-R", "<work>", "-o", "<module>.olean"]}
        records[name] = {"module": name, "source": str(path), "imports": deps,
                         "key": hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()}
        order.append(name); active.remove(name)

    visit(target)
    return {"format": FORMAT, "project": str(project), "target": target,
            "modules": [records[n] for n in order]}


def cache_valid(entry: Path, key: str, module: str) -> bool:
    try:
        manifest = json.loads((entry / "manifest.json").read_text())
        if not isinstance(manifest, dict): return False
        files = manifest["files"]
        if not isinstance(files, dict): return False
        if manifest["key"] != key or f"{module}.olean" not in files or f"{module}.out" not in files:
            return False
        return all(Path(name).name == name and
                   hashlib.sha256((entry / name).read_bytes()).hexdigest() == digest
                   for name, digest in files.items())
    except (OSError, ValueError, KeyError, TypeError):
        return False


def compile_module(name: str, work: Path, environment: dict, project: Path) -> int:
    result = subprocess.run(["lake", "env", "lean", "-R", str(work), "-o",
                             str(work / f"{name}.olean"), str(work / f"{name}.lean")],
                            cwd=project, env=environment, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (work / f"{name}.out").write_bytes(result.stdout)
    return result.returncode


def build(plan: dict, cache: Path, work: Path, compiler=compile_module, base_env=None) -> dict:
    """Cache compilation only; a failed compiler result is never cached."""
    cache.mkdir(parents=True, exist_ok=True); work.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ if base_env is None else base_env)
    environment["LEAN_PATH"] = str(work) + os.pathsep + environment.get("LEAN_PATH", "")
    results = []
    with (cache / ".lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        for item in plan["modules"]:
            name, key = item["module"], item["key"]
            entry = cache / name / key
            shutil.copy2(item["source"], work / f"{name}.lean")
            hit = cache_valid(entry, key, name)
            if hit:
                for filename in json.loads((entry / "manifest.json").read_text())["files"]:
                    shutil.copy2(entry / filename, work / filename)
            else:
                # Do not reuse stale outputs from an earlier compiler invocation.
                for path in work.glob(name + ".*"):
                    if path.suffix != ".lean": path.unlink()
                rc = compiler(name, work, environment, Path(plan["project"]))
                if rc or not (work / f"{name}.olean").is_file():
                    return {"ok": False, "failed_module": name, "exit_code": rc or 1,
                            "log": str(work / f"{name}.out"), "modules": results}
                entry.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(dir=entry.parent) as tmp:
                    stage = Path(tmp); files = {}
                    for path in work.glob(name + ".*"):
                        if path.suffix == ".lean": continue
                        shutil.copy2(path, stage / path.name)
                        files[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
                    (stage / "manifest.json").write_text(json.dumps({"key": key, "files": files}))
                    if entry.exists(): shutil.rmtree(entry)
                    shutil.copytree(stage, entry)
            results.append({"module": name, "key": key, "cache_hit": hit})
    return {"ok": True, "modules": results,
            "target_log": str(work / (plan["target"] + ".out"))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--cache", type=Path)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args()
    try:
        plan = make_plan(args.project, args.target)
        if args.plan_only: print(json.dumps(plan, indent=2)); return 0
        project = Path(plan["project"])
        expected = (project / "lean-toolchain").read_text().strip().split(":v")[-1]
        actual = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=project, text=True)
        if f"version {expected}," not in actual: raise ValueError("compiler/toolchain mismatch")
        for dep in json.loads((project / "lake-manifest.json").read_text())["packages"]:
            if dep.get("type") != "git": continue
            path = project / ".lake/packages" / dep["name"]
            revision = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
            if revision != dep["rev"]: raise ValueError(f"dependency pin mismatch: {dep['name']}")
            subprocess.run(["git", "-C", str(path), "diff", "--quiet", "HEAD", "--"], check=True)
        environment = dict(os.environ)
        environment["LEAN_PATH"] = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True).strip()
        cache = (args.cache or project / ".ci-module-cache").resolve()
        work = (args.work or project / ".ci-module-work" / args.target).resolve()
        result = build(plan, cache, work, base_env=environment)
        print(json.dumps(result, indent=2)); return 0 if result["ok"] else 1
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(json.dumps({"ok": False, "error": str(exc)})); return 1


if __name__ == "__main__":
    raise SystemExit(main())
