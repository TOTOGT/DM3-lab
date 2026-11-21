#!/usr/bin/env python3
"""Aggregate sums at several scales.  PRE-DECLARED before any run at scales 1e7, 1e8, 1e9 (21 Nov 2026):

  S(m)   = (1/(24 sigma(m))) * sum_{p in PT(P)} b_p(2m),  P = floor(2*(2m)^(1/4)),  PT(P) = primes p<=P, p = 3 mod 4
           (same as EDagg.AggSmall; b_p exact, = 2*E1 - E12).
  M(m)   = (2/3) * sum_{p in PT(P)} 2*delta_p(m),
           delta_p = 1/(p(p-1))        if p does not divide m      (density of x0=x1=0 among solutions of Q = n mod p),
           delta_p = 1/(p^3+p^2-p)     if p divides m              (same density when n = 0 mod p).
           The 2/3 is |Rmix|/(24 sigma).  M is derived from local densities mod p and is NOT adjusted after results.
  R(m)   = S(m) - M(m)                         (dimensionless)
  C(m)   = 24 sigma(m) * R(m)                  (the same residual as a count, in units of representations)
  T*(m)  = 2/3 - L(2m)   (EDagg.AggTarget bound; L = Section63b.large_primes bound).
Reported: S, M, R, C, C/m^(1/2), C/m^(3/4), C/m, R*m^(1/4), S/T*.
Counts are exact integers (int64; products r2*r2 < 4e7 per term, < 9e18 per sum); ratios are float64.
"""
import numpy as np, math, sympy, sys, time

def build_T(N):
    """T[k] = #{(a,b): a>=1, b>=0, a+b odd, a^2+b^2 = 2k+1}  for odd w=2k+1 <= N; r2(w)=4*T[k]."""
    T = np.zeros((N + 1) // 2 + 1, dtype=np.int16)
    A = math.isqrt(N)
    for a in range(1, A + 1):
        bmax = math.isqrt(N - a * a)
        b0 = 0 if a % 2 == 1 else 1
        if b0 > bmax: continue
        b = np.arange(b0, bmax + 1, 2, dtype=np.int64)
        T[(a * a + b * b - 1) // 2] += 1          # distinct b -> distinct index: no collisions
    return T

def b_p(T, n, p):
    q = p * p; vmax = n // q
    E1 = 0; CH = 1 << 24
    nv = (vmax + 1) // 2                           # odd v = 1,3,..: iv = 0..nv-1
    for s in range(0, nv, CH):
        iv = np.arange(s, min(nv, s + CH), dtype=np.int64)
        v = 2 * iv + 1
        w = n - q * v
        ok = w >= 1
        iv, w = iv[ok], w[ok]
        E1 += int((T[iv].astype(np.int64) * T[(w - 1) // 2].astype(np.int64)).sum())
    E1 *= 16
    E12 = 0
    if n % q == 0:
        h = n // q; nv2 = h // 2
        for s in range(0, nv2, CH):
            iv = np.arange(s, min(nv2, s + CH), dtype=np.int64)
            v = 2 * iv + 1; w = h - v; ok = w >= 1
            iv, w = iv[ok], w[ok]
            E12 += int((T[iv].astype(np.int64) * T[(w - 1) // 2].astype(np.int64)).sum())
        E12 *= 16
    return 2 * E1 - E12

def evaluate(T, m):
    n = 2 * m; P = math.floor(2 * n ** 0.25)
    PT = [p for p in sympy.primerange(2, P + 1) if p % 4 == 3]
    sig = int(sympy.divisor_sigma(m))
    tot = sum(b_p(T, n, p) for p in PT)
    S = tot / (24 * sig)
    M = (2 / 3) * sum(2 * (1 / (p * (p - 1)) if m % p else 1 / (p ** 3 + p ** 2 - p)) for p in PT)
    u = n ** (1 / 20)
    L = (4 / 3) * (11 / 5 * u ** 4) * (2 / (15 * P) + 2 / P ** 2 + (2 * u ** 10 / 15 + 1) / u ** 20)
    Ts = 2 / 3 - L
    R = S - M; C = 24 * sig * R
    return dict(m=m, n=n, P=P, npr=len(PT), sig=sig, tot=tot, S=S, M=M, R=R, C=C,
                C_half=C / m ** 0.5, C_34=C / m ** 0.75, C_1=C / m, Rm14=R * m ** 0.25, ratio=S / Ts, Ts=Ts)

def pick(scale, k):
    """k odd m near `scale`, all prime factors = 3 mod 4 (as in Prop 6.1), mixed factorization types."""
    out = []; m = scale | 1
    while len(out) < k:
        m += 2
        f = sympy.factorint(m)
        if all(p % 4 == 3 for p in f): out.append(m)
    return out

if __name__ == "__main__":
    scale = int(float(sys.argv[1])); k = int(sys.argv[2])
    ms = pick(scale, k) if len(sys.argv) < 4 else [int(x) for x in sys.argv[3:]]
    t0 = time.time(); N = 2 * max(ms) + 2
    T = build_T(N); t1 = time.time()
    print(f"# scale {scale:.0e}: table to N={N} built in {t1-t0:.0f}s (int16 counts, exact); host int64/float64", flush=True)
    for m in ms:
        t = time.time(); r = evaluate(T, m)
        print("m={m} n={n} P={P} #p={npr} sigma={sig} sum_b={tot}\n  S={S:.6f} M={M:.6f} R={R:+.3e} C={C:+.4e}  C/m^.5={C_half:+.3f}  C/m^.75={C_34:+.4f}  C/m={C_1:+.5f}  R*m^.25={Rm14:+.4f}  S/T*={ratio:.4f} (T*={Ts:.4f})".format(**r), f" [{time.time()-t:.0f}s]", flush=True)
