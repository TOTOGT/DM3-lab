#!/usr/bin/env python3
"""Census of Lean theorems/lemmas across every git repo under the given roots.

Counts declared `theorem`/`lemma` names (namespace-qualified), per repo and globally, after stripping comments.
It does NOT establish that anything compiles. Per file it only records: sorry in code, `axiom` declarations,
native_decide, and `#print axioms` lines. 'clean' = declared in a file with no sorry and no axiom declaration; 'axrep' = clean and the file has #print axioms lines. Neither proves the file compiles.
Excludes .lake, build, packages, node_modules. Usage: theorems-census.py ROOT [ROOT ...] [--json out.json]
"""
import os, re, sys, json, hashlib, collections

SKIP = {'.lake', 'build', 'node_modules', 'packages', '.git', '_to_delete'}
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe)\s+)*(theorem|lemma)\s+([^\s:({\[]+)')
NS = re.compile(r'^\s*namespace\s+(\S+)')
END = re.compile(r'^\s*end\s*(\S*)')
SEC = re.compile(r'^\s*section\b\s*(\S*)')

def strip_comments(t):
    out, i, depth = [], 0, 0
    while i < len(t):
        if t.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and t.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            out.append('\n' if t[i] == '\n' else ' '); i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i); i = len(t) if j < 0 else j; continue
        out.append(t[i]); i += 1
    return ''.join(out)

def parse(path):
    try:
        raw = open(path, encoding='utf-8', errors='replace').read()
    except Exception:
        return None
    code = strip_comments(raw)
    stack, names = [], []
    for line in code.split('\n'):
        m = NS.match(line)
        if m:
            stack.append(('ns', m.group(1))); continue
        m = SEC.match(line)
        if m and not line.strip().startswith('sectioned'):
            stack.append(('sec', m.group(1))); continue
        m = END.match(line)
        if m and stack:
            stack.pop(); continue
        m = DECL.match(line)
        if m:
            q = '.'.join([n for k, n in stack if k == 'ns'] + [m.group(2)])
            names.append(q)
    return dict(
        names=names,
        sorry=len(re.findall(r'\bsorry\b', code)),
        axioms=len(re.findall(r'^\s*axiom\b', code, re.M)),
        native=len(re.findall(r'native_decide', code)),
        printax=len(re.findall(r'#print axioms', code)),
        sha=hashlib.sha1(raw.encode('utf-8', 'replace')).hexdigest(),
    )

def repo_roots(roots):
    found = []
    for r in roots:
        for dp, dn, fn in os.walk(r):
            dn[:] = [d for d in dn if d not in SKIP or d == '.git']
            if '.git' in dn or '.git' in fn:
                found.append(dp)
            dn[:] = [d for d in dn if d != '.git']
    return sorted(set(found), key=len, reverse=True)

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    jout = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else None
    if jout and jout in args: args.remove(jout)
    roots = repo_roots(args)
    per = collections.OrderedDict()
    seen_files = {}
    for r in roots:
        per[r] = dict(files=0, dup_files=0, distinct=set(), clean=set(), rep=set(), sorry_files=0, axiom_files=0, native_files=0, lines=0)
    for base in args:
        for dp, dn, fn in os.walk(base):
            dn[:] = [d for d in dn if d not in SKIP]
            for f in fn:
                if not f.endswith('.lean'): continue
                p = os.path.join(dp, f)
                repo = next((r for r in roots if p.startswith(r + os.sep)), None)
                if repo is None: continue
                info = parse(p)
                if info is None: continue
                s = per[repo]
                if info['sha'] in seen_files:
                    s['dup_files'] += 1; continue
                seen_files[info['sha']] = p
                s['files'] += 1
                s['sorry_files'] += info['sorry'] > 0
                s['axiom_files'] += info['axioms'] > 0
                s['native_files'] += info['native'] > 0
                for n in info['names']:
                    s['distinct'].add(n)
                    if info['sorry'] == 0 and info['axioms'] == 0:
                        s['clean'].add(n)
                        if info['printax'] > 0:
                            s['rep'].add(n)
    all_d, all_c, all_r = set(), set(), set()
    rows = []
    for r, s in per.items():
        if s['files'] == 0: continue
        all_d |= s['distinct']; all_c |= s['clean']; all_r |= s['rep']
        rows.append((os.path.relpath(r, os.path.expanduser('~')), s['files'], s['dup_files'], len(s['distinct']), len(s['clean']), len(s['rep']), s['sorry_files'], s['axiom_files'], s['native_files']))
    rows.sort(key=lambda x: -x[3])
    print(f"{'repo':46} {'files':>5} {'dupes':>5} {'distinct':>8} {'clean':>6} {'axrep':>6} {'sorryF':>6} {'axiomF':>6} {'nativeF':>7}")
    for x in rows:
        print(f"{x[0][:46]:46} {x[1]:5} {x[2]:5} {x[3]:8} {x[4]:6} {x[5]:6} {x[6]:6} {x[7]:6} {x[8]:7}")
    print()
    print(f"unique files (by content): {len(seen_files)}")
    print(f"distinct qualified names, all repos (lower bound; same name in two repos counts once): {len(all_d)}")
    print(f"  of which declared in files with no sorry and no axiom: {len(all_c)}")
    print(f"  of which also in a file that prints axiom reports (#print axioms): {len(all_r)}")
    if jout:
        json.dump(dict(rows=rows, distinct=len(all_d), clean=len(all_c), axrep=len(all_r), files=len(seen_files)), open(jout, 'w'), indent=1)

if __name__ == '__main__':
    main()
