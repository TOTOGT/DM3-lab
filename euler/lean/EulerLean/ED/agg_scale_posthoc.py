#!/usr/bin/env python3
"""POST-HOC diagnostic (written after seeing the pre-declared run of agg_scale.py; does not replace it).
The pre-declared M gave a nonzero density for primes p | m.  Elementary fact (independent of any data):
if p = 3 mod 4 and p | x0, p | x1, p | n = sum x_i^2, then p | x2^2 + x3^2, hence p | x2, p | x3 (since -1 is a
non-residue), hence p^2 | n.  So b_p(n) = 0 whenever v_p(n) = 1, i.e. v_p(m) = 1 (n = 2m, p odd).
M2 keeps the pre-declared delta_p for p not dividing m, uses delta_p = 0 for v_p(m) = 1, and keeps the pre-declared
value for v_p(m) >= 2 (flagged: no derivation).  Also prints b_p for each p | m as a direct check of the identity."""
import sys, math, sympy
from agg_scale import build_T, b_p, evaluate
scale = int(float(sys.argv[1])); ms = [int(x) for x in sys.argv[2:]]
T = build_T(2 * max(ms) + 2)
for m in ms:
    r = evaluate(T, m); n = 2 * m; f = sympy.factorint(m)
    P = r['P']; PT = [p for p in sympy.primerange(2, P + 1) if p % 4 == 3]
    flag = any(f.get(p, 0) >= 2 for p in PT)
    M2 = (2 / 3) * sum(2 * (1 / (p * (p - 1)) if m % p else (0.0 if f[p] == 1 else 1 / (p ** 3 + p ** 2 - p))) for p in PT)
    R2 = r['S'] - M2; C2 = 24 * r['sig'] * R2
    bps = {p: b_p(T, n, p) for p in PT if m % p == 0}
    print(f"m={m} factors={f}  b_p for p|m: {bps}")
    print(f"  S={r['S']:.6f} M2={M2:.6f} R2={R2:+.3e} C2={C2:+.4e}  C2/m^.5={C2/m**.5:+.3f}  C2/m^.75={C2/m**.75:+.4f}  C2/m={C2/m:+.5f}  v_p>=2 for some p<=P: {flag}", flush=True)
