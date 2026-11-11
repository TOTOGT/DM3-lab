#!/usr/bin/env python3
"""
extract_names.py <root_dir>

Walks root_dir for .lean files and extracts every top-level theorem/lemma
declaration name (comment-stripped, so text inside /- -/ or -- comments is
never mistaken for a real declaration), FULLY QUALIFIED by any enclosing
`namespace ... end` blocks.

This matters because `#print axioms <name>` needs a name Lean can actually
resolve. A theorem declared as `isLipschitz` inside `namespace GCTC` /
`namespace Compressor` is only accessible as `GCTC.Compressor.isLipschitz`
(or via `open`) — the bare name doesn't resolve, which is exactly what
the first real CI run against this file caught (every name came back
"unknown constant" until this namespace-tracking was added).

Output: one line per declaration, tab-separated:
    relative/path.lean<TAB>kind<TAB>fully.qualified.name

This is the input list that make_axiom_probe.py turns into a real
`#print axioms` probe file, and that parse_axiom_output.py cross-checks
the real compiler output against.
"""
import os
import re
import sys

DECL_RE = re.compile(
    r'^\s*(?:@\[.*?\]\s*)?(?:private |protected |noncomputable )*(theorem|lemma)\s+'
    r'([^\s:({\[]+)'
)
NAMESPACE_OPEN_RE = re.compile(r'^\s*namespace\s+(\S+)')
NAMESPACE_END_RE = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
SECTION_OPEN_RE = re.compile(r'^\s*section\b(?:\s+(\S+))?')


def strip_lean_comments(text: str) -> str:
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if text[i:i + 2] == '/-':
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text[i:i + 2] == '-/':
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        out.append(text[i])
        i += 1
    stripped = ''.join(out)
    lines = []
    for line in stripped.split('\n'):
        idx = line.find('--')
        if idx != -1:
            line = line[:idx]
        lines.append(line)
    return '\n'.join(lines)


def extract(text: str):
    """Yield (kind, fully_qualified_name) walking the file line by line,
    tracking a stack of enclosing namespace/section names. `section` without
    a name doesn't affect qualification (anonymous sections don't qualify
    names in Lean 4), only named `namespace`/`section NAME` do."""
    stack = []
    results = []
    for line in text.split('\n'):
        m = NAMESPACE_OPEN_RE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = SECTION_OPEN_RE.match(line)
        if m and m.group(1):
            stack.append(m.group(1))
            continue
        m = NAMESPACE_END_RE.match(line)
        if m:
            if stack:
                stack.pop()
            continue
        m = DECL_RE.match(line)
        if m:
            kind, name = m.group(1), m.group(2)
            qualified = '.'.join(stack + [name]) if stack else name
            results.append((kind, qualified))
    return results


def main():
    if len(sys.argv) != 2:
        print("usage: extract_names.py <root_dir>", file=sys.stderr)
        sys.exit(1)
    root = sys.argv[1]
    for dirpath, dirnames, filenames in os.walk(root):
        if '.lake' in dirpath.split(os.sep) or '.git' in dirpath.split(os.sep):
            continue
        for fn in filenames:
            if not fn.endswith('.lean'):
                continue
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, root)
            try:
                with open(full, encoding='utf-8', errors='ignore') as f:
                    text = f.read()
            except OSError:
                continue
            stripped = strip_lean_comments(text)
            for kind, name in extract(stripped):
                print(f"{rel}\t{kind}\t{name}")


if __name__ == '__main__':
    main()
