#!/usr/bin/env python3
"""
check_site.py -- checks index.html against its sources instead of trusting the sentences.

  [1] structure: every status chip uses an allowed class; every in-page link target exists;
      only https:, mailto:, #anchor links and relative links to files that exist.
  [2] wording: phrases the V5 narrowing withdrew must not appear as claims.
      'Coherence Bridge' and 'helical' may appear only in the Withdrawn row.
  [3] sources (needs sibling clones ../io and ../geometry; skipped with a notice if absent):
      DOIs, the 200000 trial count, the commit hash, the scripts named on the page.
  Controls: each check type is also run on a doctored input and must FAIL there.

Run:  python3 check_site.py
"""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PAGE = open(os.path.join(HERE, 'index.html'), encoding='utf-8').read()
FAIL = []
def check(name, ok, note=''):
    print('  [%s] %s' % ('PASS' if ok else 'FAIL', name) + (('  -- ' + note) if note and not ok else ''))
    if not ok: FAIL.append(name)
def control(name, would_pass):
    print('  [%s] control: %s' % ('OK  ' if not would_pass else 'BLIND', name))
    if would_pass: FAIL.append('blind control: ' + name)

ALLOWED = {'verified','checked','derived','open','unaudited','withdrawn','progress'}
def chips_ok(html):
    used = set(re.findall(r'class="chip c-([a-z]+)"', html))
    return used <= ALLOWED and len(used) > 0
def links_ok(html):
    ids = set(re.findall(r'\bid="([^"]+)"', html))
    for h in re.findall(r'href="([^"]*)"', html):
        if h.startswith('#'):
            if h[1:] not in ids: return False
        elif h.startswith('https://') or h.startswith('mailto:'): pass
        elif '://' in h or ':' in h: return False
        elif not os.path.exists(os.path.join(HERE, h)): return False
    return True
def wording_ok(html):
    body = re.sub(r'<tr><td class="item">Coherence Bridge.*?</tr>', '', html, flags=re.S)
    return not re.search(r'Coherence Bridge|helical attractor|helical phase|unified theory|Millennium', body, re.I)

print('[1] structure')
check('status chips use allowed classes', chips_ok(PAGE))
check('links: https, mailto, or an anchor that exists', links_ok(PAGE))
control('an unknown chip class must fail', chips_ok('<span class="chip c-proven">x</span>'))
control('a dead #anchor must fail', links_ok('<a href="#nowhere">x</a><div id="a"></div>'))
control('an http: link must fail', links_ok('<a href="http://example.com">x</a>'))
control('a relative link to a missing file must fail', links_ok('<a href="no-such-file.html">x</a>'))
check('the legacy homepage the footer points to exists', os.path.exists(os.path.join(HERE, 'index-legacy.html')))
print('[2] wording')
check('withdrawn claims do not appear outside the Withdrawn row', wording_ok(PAGE))
control('a doctored page that claims a Coherence Bridge must fail', wording_ok(PAGE.replace('Origin', 'Origin: the Coherence Bridge unifies seven fields', 1)))

print('[3] sources')
io, geo = os.path.join(HERE, '..', 'io'), os.path.join(HERE, '..', 'geometry')
def read(p):
    try: return open(p, encoding='utf-8', errors='replace').read()
    except OSError: return None
if not (os.path.isdir(io) and os.path.isdir(geo)):
    print('  [SKIP] sibling clones ../io and ../geometry not found; source checks not run')
else:
    gcm = read(os.path.join(geo, 'gcm-framework.html')); gv = read(os.path.join(geo, 'gcm-framework-verify.py'))
    iop = read(os.path.join(io, 'index.html'))
    check('GCM DOI 20230610 is on the GCM page', '10.5281/zenodo.20230610' in (gcm or '') and '10.5281/zenodo.20230610' in PAGE)
    check('V6 DOI 22929142 is on the io page', '10.5281/zenodo.22929142' in (iop or '') and '10.5281/zenodo.22929142' in PAGE)
    check('GCM verifier uses 200000 trials', 'range(200000)' in (gv or '') and '200,000' in PAGE)
    check('GCM page lists eight axioms and four theorems', 'Eight Axioms' in (gcm or '') and 'Theorem D' in (gcm or ''))
    for f in ('fixed_norm_width_check.py', 'cage_threshold_check.py'):
        check('io/scripts/%s exists and is named on the page' % f, os.path.exists(os.path.join(io, 'scripts', f)) and f in PAGE)
    try:
        out = subprocess.run(['git', '--no-optional-locks', '-C', io, 'cat-file', '-t', '6127948'], capture_output=True, text=True).stdout.strip()
        check('io commit 6127948 exists', out == 'commit')
    except Exception as e:
        check('io commit 6127948 exists', False, str(e))
    check('io page says 28/28 for the current file', '<strong>28/28</strong>' in (iop or '') and '28 of 28' in PAGE)
    control('a wrong DOI must fail', '10.5281/zenodo.99999999' in (gcm or ''))

print()
if FAIL: print('FAILED:', FAIL); sys.exit(1)
print('ALL CHECKS PASSED. This checks the page against its sources; it does not re-run any Lean or any experiment.')
