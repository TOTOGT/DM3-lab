#!/usr/bin/env python3
"""FROZEN BEFORE ANY RUN (21 Nov 2026).  Per-prime count b_p(2m) for p = 3 (mod 4), p NOT dividing m.  HPrime/H31ndvd/AggTarget stay OPEN.

Setting: n = 2m, m odd, p prime = 3 mod 4, p not | m (so p not | n).  Rmix(n) = {x in Z^4 : sum x^2 = n, x0+x1 odd, x2+x3 odd}, |Rmix| = 16 sigma(m).
b_p(n) = |E1 u E2|, E1 = {x in Rmix: p|x0,x1}, E2 = {p|x2,x3}.  E1 n E2 = {} (else p^2 | n), so b_p = 2|E1|.
Exact reduction (p odd): x0=pu, x1=pv, u+v odd <=> a=u^2+v^2 odd; then w = n - p^2 a is odd and x2+x3 odd <=> w odd, so
     |E1| = sum_{a odd, p^2 a <= n} r2(a) r2(n - p^2 a),      b_p = 2|E1|        (r2 = number of reps as a sum of two squares).
Local density (same method as AGG-PADIC.md, checked there by exact counts mod p^s for k=0 as well):
  sigma_p(n) = 1 - p^-2 (p not | n);  with p|x0,x1 the box has measure p^-2 and the binary norm form N(x2,x3) at w = n - p^2 N(u,v),
  w a unit, has density (1 + 1/p);  conditional density r_p(0) = p^-2 (1+1/p)/(1-p^-2) = 1/(p(p-1)).  NO distinction between p = 3 and p > 3
  at the level of local density; n mod p plays no role (norm form of the unramified extension is uniform on units).
Prediction (main term, normalized by 24 sigma(m)):   Mp(m) = b_p/(24 sigma) ~ (2/3) * 2/(p(p-1)) = 4/(3 p (p-1)).
  [Per-prime bound in H31ndvd is 2/(p(p-1)) + (E if p>3 else 0), E = tau(m) sqrt(m)/(3 sigma(m)); main term is 2/3 of the bound, so room = 1/3 of the bound.]
Reported per (m,p): b_p, b_p/(24 sigma), Mp, signed residual rho = b_p/(24 sigma) - Mp, Eallow = tau(m)sqrt(m)/(3 sigma(m)), rho/Eallow,
  rho*24*sigma/sqrt(m) (absolute residual in m^(1/2) units), and slack = [2/(p(p-1)) + (Eallow if p>3 else 0)] - b_p/(24 sigma) (H31ndvd holds iff >= 0).
Part A: exhaustive scan, all odd m <= MA with 3 not | m, p = 3 (extreme values of b_3/(8 sigma) and the sign/size of rho), plus brute-force cross-check of
  the reduction against direct enumeration of Rmix for small m.
Part B: fresh m (not used in any earlier test), scales 1e7,1e8,1e9, p in {3,7,11,19,23,31,43}, p not | m, m odd with all prime factors = 3 mod 4.
No main term is adjusted after seeing results; anything added later is labelled post-hoc.
"""
import sys, math, time, itertools, numpy as np, sympy
from agg_scale import build_T, b_p

def Mp(p): return 4 / (3 * p * (p - 1))

def brute_bp(n, p):
    R = int(math.isqrt(n)); c = 0
    for x0 in range(-R, R + 1):
        for x1 in range(-R, R + 1):
            if (x0 + x1) % 2 == 0 or x0*x0 + x1*x1 > n: continue
            for x2 in range(-R, R + 1):
                r = n - x0*x0 - x1*x1 - x2*x2
                if r < 0: continue
                x3 = math.isqrt(r)
                if x3 * x3 != r: continue
                for y in {x3, -x3}:
                    if (x2 + y) % 2 == 0: continue
                    if (x0 % p == 0 and x1 % p == 0) or (x2 % p == 0 and y % p == 0): c += 1
    return c

def row(T, m, p):
    n = 2 * m; sig = int(sympy.divisor_sigma(m)); tau = int(sympy.divisor_count(m))
    b = b_p(T, n, p); q = b / (24 * sig); E = tau * math.sqrt(m) / (3 * sig)
    rho = q - Mp(p); bound = 2 / (p * (p - 1)) + (E if p > 3 else 0)
    return dict(m=m, p=p, b=b, q=q, rho=rho, E=E, rho_E=rho / E, rho_abs=rho * 24 * sig / math.sqrt(m), slack=bound - q, q_over_bound=q / (2 / (p*(p-1))), sig=sig)

def partA(MA):
    T = build_T(2 * MA + 2)
    print("# cross-check of the reduction against brute-force enumeration of Rmix")
    ok = True
    for m, p in [(1,3),(5,3),(7,3),(11,3),(13,3),(17,3),(19,7),(23,7),(29,7),(35,3),(37,7),(41,3),(43,3),(47,7)]:
        if m % p == 0: continue
        a = b_p(T, 2*m, p); b = brute_bp(2*m, p); ok &= (a == b)
        print(f"  m={m:3d} p={p}: reduction {a:6d}  brute {b:6d}  {'OK' if a==b else 'MISMATCH'}")
    print("  ALL OK" if ok else "  MISMATCH PRESENT")
    sieve_sig = np.zeros(MA + 1, dtype=np.int64)
    for d in range(1, MA + 1): sieve_sig[d::d] += d
    rows = []; worst = None
    for m in range(1, MA + 1, 2):
        if m % 3 == 0: continue
        n = 2 * m; b = b_p(T, n, 3); sig = int(sieve_sig[m])
        rows.append((m, b / (8 * sig), b / (24 * sig) - Mp(3), b))
    arr = np.array([(r[1], r[2]) for r in rows])
    print(f"# Part A: p=3, all odd m<={MA}, 3 not | m: {len(rows)} values")
    print(f"  max b_3/(8 sigma) (=b/(24sigma)/(1/3); must stay <1 for H31ndvd at p=3): {arr[:,0].max():.4f} at m={rows[int(arr[:,0].argmax())][0]}")
    print(f"  mean ratio {arr[:,0].mean():.4f} (main term predicts 2/3 = 0.6667)")
    print(f"  residual rho = b/(24 sigma) - 2/9: min {arr[:,1].min():+.4f}, max {arr[:,1].max():+.4f}, mean {arr[:,1].mean():+.5f}")
    top = sorted(rows, key=lambda r: -r[1])[:10]
    print("  ten largest b_3/(8 sigma):", [(r[0], round(r[1], 4)) for r in top])
    # by size
    for lo, hi in [(1,100),(100,1000),(1000,10000),(10000,MA)]:
        sub = [r for r in rows if lo <= r[0] < hi]
        if sub: print(f"  m in [{lo},{hi}): n={len(sub):6d} max ratio {max(r[1] for r in sub):.4f}  max|rho| {max(abs(r[2]) for r in sub):.4f}")
    return rows

def fresh(scale, p, off):
    m = scale + off | 1
    while True:
        m += 2
        if m % p == 0: continue
        if all(q % 4 == 3 for q in sympy.factorint(m)): return m

def partB():
    PS = [3, 7, 11, 19, 23, 31, 43]
    print("# Part B (fresh m)")
    print("scale | m | factorisation | p | b_p | b/(24s) | Mp | rho | Eallow | rho/Eallow | rho_abs/m^.5 | slack>=0 | b/bound")
    for scale in (10**7, 10**8, 10**9):
        t0 = time.time(); ms = [fresh(scale, 3, 777 + 1000 * i) for i in range(3)]
        T = build_T(2 * max(ms) + 2)
        for m in ms:
            f = "*".join(f"{q}^{e}" if e > 1 else f"{q}" for q, e in sympy.factorint(m).items())
            for p in PS:
                if m % p == 0: continue
                r = row(T, m, p)
                print(f"{scale:.0e} | {m} | {f} | {p} | {r['b']} | {r['q']:.6f} | {Mp(p):.6f} | {r['rho']:+.3e} | {r['E']:.3e} | {r['rho_E']:+.3e} | {r['rho_abs']:+.3f} | {'yes' if r['slack']>=0 else 'NO'} | {r['q_over_bound']:.4f}", flush=True)
        print(f"# scale {scale:.0e} done in {time.time()-t0:.0f}s", flush=True)

if __name__ == "__main__":
    if sys.argv[1] == "A": partA(int(sys.argv[2]))
    else: partB()
