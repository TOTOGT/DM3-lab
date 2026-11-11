#!/usr/bin/env python3
"""
make_axiom_probe.py <names_file> <import_root>

Reads the tab-separated (file, kind, name) list produced by extract_names.py
and emits a single .lean file that imports the whole library and then runs
the real, built-in `#print axioms <name>` command for every declaration.

This deliberately does NOT reimplement axiom-collection logic — it uses
Lean's own `#print axioms` command, which is the same command a human would
type interactively. The only work here is generating one line per theorem
and, later, parsing the real compiler output back into a table.

Known limitation (honest, since this couldn't be test-compiled locally):
if a name isn't resolvable at the top level (e.g. it's shadowed, or lives
in a namespace not opened here), Lean will report an error for that single
line instead of axiom info — parse_axiom_output.py treats that as
'name-not-resolvable' rather than crashing, so one bad name doesn't take
down the whole probe.
"""
import sys

def main():
    if len(sys.argv) != 3:
        print("usage: make_axiom_probe.py <names_file> <import_root>", file=sys.stderr)
        sys.exit(1)
    names_file, import_root = sys.argv[1], sys.argv[2]

    print(f"import {import_root}")
    print()

    seen = set()
    with open(names_file, encoding='utf-8') as f:
        for line in f:
            line = line.rstrip('\n')
            if not line:
                continue
            parts = line.split('\t')
            if len(parts) != 3:
                continue
            _relpath, _kind, name = parts
            if name in seen:
                continue
            seen.add(name)
            # #print axioms is the real, built-in Lean command.
            print(f"#print axioms {name}")


if __name__ == '__main__':
    main()
