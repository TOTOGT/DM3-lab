#!/usr/bin/env python3
"""Check exact Lean #print axioms reports, without borrowing adjacent reports.

Usage: python3 check_axioms.py LOG THEOREM [THEOREM ...]
Exit 0 means each requested theorem has exactly one complete report whose axiom
set is a subset of the explicit allowlist. This does not inspect theorem types
or discharge their hypotheses; compilation must be checked separately.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
from typing import Any


DEFAULT_ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
REPORT_START = re.compile(
    r"^'(?P<name>[^'\r\n]+)' (?:(?P<list>depends on axioms:)"
    r"|(?P<none>does not depend on any axioms)[ \t]*$)",
    re.MULTILINE,
)


def parse_reports(text: str) -> dict[str, list[dict[str, Any]]]:
    starts = list(REPORT_START.finditer(text))
    reports: dict[str, list[dict[str, Any]]] = {}
    for index, match in enumerate(starts):
        record: dict[str, Any] = {"axioms": [], "error": None}
        if match.group("list"):
            end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
            remainder = text[match.end():end]
            opening = re.match(r"\s*\[", remainder)
            if opening is None:
                record["error"] = "axiom report has no opening bracket"
            else:
                closing = remainder.find("]", opening.end())
                if closing == -1:
                    record["error"] = "axiom report is unterminated before the next report"
                else:
                    contents = remainder[opening.end():closing]
                    if "[" in contents:
                        record["error"] = "axiom report contains a nested opening bracket"
                    elif contents.strip():
                        names = [part.strip() for part in contents.split(",")]
                        if any(not name for name in names):
                            record["error"] = "axiom report contains an empty entry"
                        else:
                            record["axioms"] = names
        reports.setdefault(match.group("name"), []).append(record)
    return reports


def check_reports(
    text: str, targets: list[str], allowed: frozenset[str] = DEFAULT_ALLOWED
) -> dict[str, Any]:
    reports = parse_reports(text)
    results: list[dict[str, Any]] = []
    for name in targets:
        records = reports.get(name, [])
        result: dict[str, Any] = {"name": name, "ok": False, "axioms": [], "error": None}
        if not records:
            result["error"] = "missing exact declaration report"
        elif len(records) != 1:
            result["error"] = f"duplicate declaration reports ({len(records)})"
        elif records[0]["error"]:
            result["error"] = records[0]["error"]
        else:
            result["axioms"] = records[0]["axioms"]
            rejected = sorted(set(result["axioms"]) - allowed)
            if rejected:
                result["error"] = "disallowed axioms: " + ", ".join(rejected)
            else:
                result["ok"] = True
        results.append(result)
    return {
        "ok": bool(targets) and all(result["ok"] for result in results),
        "allowed_axioms": sorted(allowed),
        "targets": results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("theorems", nargs="+")
    parser.add_argument("--allow", action="append", help="Override the default allowlist")
    args = parser.parse_args()
    allowed = DEFAULT_ALLOWED if args.allow is None else frozenset(args.allow)
    try:
        text = args.log.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        print(json.dumps({"ok": False, "error": str(error)}))
        return 1
    result = check_reports(text, args.theorems, allowed)
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
