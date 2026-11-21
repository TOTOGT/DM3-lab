#!/usr/bin/env python3
"""FROZEN BEFORE ANY TEST ON FRESH m (21 Nov 2026).  p-adic correction for primes p = 3 (mod 4) dividing m.

Setting.  n = 2m, m odd, p = 3 mod 4 prime, k = v_p(m) = v_p(n).  Q(x) = x0^2+x1^2+x2^2+x3^2.
b_p(n) = #{x in Rmix : p|x0,x1  or  p|x2,x3} = 2*E1 - E12  (as in EDagg / agg_true.py).

Derivation (checked by brute force mod p^s in local_density_check.py: p=3 k=1..4, p=7,11,19 k=1,2, all OK):
 1. Q is unimodular of discriminant 1 over Z_p, Q = H + H.  Local density
        sigma_p(n)   = (1 - p^-2) * (1 + p^-1 + ... + p^-k).
 2. Constraint p | x0, p | x1:  write x0 = p*u, x1 = p*v.  This contributes the factor p^-2 (the box has p^-2 of the
    measure) times the density of the remaining binary norm form N(x2,x3) = x2^2+x3^2 (anisotropic, unramified)
    at w = n - p^2 N(u,v).  N has density (1+1/p)*[v_p(w) even].  With (u,v) Haar-random, P[v_p(n - p^2 N(u,v)) even]
    equals 0 for k = 1, and 1 - p^-(k-1) for k >= 2 (computed by splitting on v_p(u,v) = a and a uniform unit norm;
    the same closed form holds for even and odd k-2).  Hence
        sigma_p^c(n) = p^-2 (1 + 1/p) (1 - p^-(k-1))   (k >= 1),     sigma_p^c(n) = p^-2 (1 + 1/p)   (k = 0).
 3. Conditional density (NOT simply p^-2):
        r_p(0) = 1/(p(p-1)),     r_p(k) = (p^(k-1) - 1) / (p^(k+1) - 1)   for k >= 1
    (r_p(1) = 0, r_p(2) = 1/(p^2+p+1), r_p(3) = 1/(p^2+1), r_p(4) = (p^3-1)/(p^5-1)).
 4. Contribution to b_p.  For k = 0 the two pair-events are disjoint: b_p ~ 2 |Rmix| r_p(0).  For k >= 1,
    p | x0,x1 and p | n force p | x2^2+x3^2, hence p | x2, x3 (-1 is a non-residue mod p): the events coincide,
    E1 = E2 = E12 and b_p ~ |Rmix| r_p(k) (no factor 2).
 5. EXACT identity (no asymptotics), same argument: for p | m,  b_p(2m) = #{y : Q(y) = 2m/p^2, parity conditions}
        = 16 * sigma(m/p^2)  if p^2 | m,     b_p(2m) = 0  if p || m.
    Consistent with step 3: sigma(m/p^2)/sigma(m) = r_p(k).
 Prediction of the correction: S(m) - M3(m) should be of the same size as for squarefree-coprime m (C = O(m^(1/2)))
 and b_p must equal 16*sigma(m/p^2) EXACTLY for every p | m with p <= P.

Main terms (all dimensionless, divided by 24*sigma(m)):
  M  (pre-declared in agg_scale.py)  : (2/3) sum_p 2*delta_p, delta_p = 1/(p(p-1)) (p not | m), 1/(p^3+p^2-p) (p | m).
  M2 (post-hoc, agg_scale_posthoc.py): as M but delta_p = 0 for v_p(m) = 1.
  M3 (this file, frozen now)         : (2/3) sum_p w_p, w_p = 2/(p(p-1)) if k = 0; w_p = r_p(k) if k >= 1 (equal to the exact
                                       b_p/(16 sigma(m)) for p | m).
Reported: S, M, M2, M3, residuals R=S-M*, C=24 sigma R, C/m^(1/2), C/m^(3/4), C/m, S/T*, and the exact-identity check.
Fresh m: for scale in 1e7, 1e8, 1e9 and (p,k) in LIST: smallest m >= scale with p^k || m, cofactor odd with all prime
factors = 3 mod 4.  The diagnostic m = 10000053 is reported separately and is not a test point.
"""
import sys, math, time, sympy
from agg_scale import build_T, b_p, evaluate

LIST = [(3, 2), (3, 3), (3, 4), (7, 2), (7, 3), (11, 2), (19, 2), (23, 2)]

def r(p, k): return 1 / (p * (p - 1)) if k == 0 else (p ** (k - 1) - 1) / (p ** (k + 1) - 1)

def fresh(scale, p, k):
    m = scale
    while True:
        m += 1
        if m % 2 == 0 or m % (p ** k) or (m // p ** k) % p == 0: continue
        if all(q % 4 == 3 for q in sympy.factorint(m)): return m

def one(T, m, tag=""):
    res = evaluate(T, m); n = 2 * m; P = res['P']; f = sympy.factorint(m)
    PT = [p for p in sympy.primerange(2, P + 1) if p % 4 == 3]
    M3 = (2 / 3) * sum((2 * r(p, 0)) if m % p else r(p, f[p]) for p in PT)
    M2 = (2 / 3) * sum(2 * (1 / (p * (p - 1)) if m % p else (0.0 if f[p] == 1 else 1 / (p ** 3 + p ** 2 - p))) for p in PT)
    exact_ok, bad = True, []
    for p in PT:
        if m % p == 0:
            want = 16 * int(sympy.divisor_sigma(m // p ** 2)) if f[p] >= 2 else 0
            got = b_p(T, n, p)
            if got != want: exact_ok = False; bad.append((p, got, want))
    out = []
    for name, MM in (("M ", res['M']), ("M2", M2), ("M3", M3)):
        R = res['S'] - MM; C = 24 * res['sig'] * R
        out.append(f"   {name}: main={MM:.6f} R={R:+.3e} C={C:+.4e} C/m^.5={C/m**.5:+.3f} C/m^.75={C/m**.75:+.4f} C/m={C/m:+.5f}")
    fs = "*".join(f"{p}^{e}" if e > 1 else str(p) for p, e in f.items())
    print(f"m={m} {tag}= {fs}  S={res['S']:.6f} S/T*={res['ratio']:.4f}  exact b_p=16*sigma(m/p^2) / 0 for all p|m, p<=P: {'YES' if exact_ok else 'NO ' + str(bad)}")
    print("\n".join(out), flush=True)

if __name__ == "__main__":
    scale = int(float(sys.argv[1])); t0 = time.time()
    ms = [(fresh(scale, p, k), f"({p}^{k})") for p, k in LIST]
    if scale == 10 ** 7: ms.append((10000053, "(DIAGNOSTIC, original case)"))
    T = build_T(2 * max(m for m, _ in ms) + 2)
    print(f"# scale {scale:.0e}: table N={2*max(m for m,_ in ms)+2} built in {time.time()-t0:.0f}s; exact int64 counts, float64 ratios", flush=True)
    for m, tag in ms: one(T, m, tag)
    print(f"# total {time.time()-t0:.0f}s")
