#!/usr/bin/env python3
"""EXPLORATORY (found by inspection of Part A/B output, 21 Nov 2026; labelled post-hoc).  Test of the observed exact relation
   b_3(2m) = (16/3) * (sigma(m) - c(m))     for odd m, 3 not | m,
where sum c(n) q^n = q * prod_{k>=1} (1 - q^{6k})^4 = eta(6z)^4 (c(n)=0 unless n = 1 mod 6; the weight-2 CM newform of level 36).
Not a derivation; the relation was read off numerically for odd m <= 4000 (1333 values, no exception).  This script tests it on all odd m <= MA
(fresh range beyond 4000) and reports the consequence for the p=3 case of H31ndvd:  b_3 <= 8 sigma  <=>  c(m) >= -sigma(m)/2."""
import sys, numpy as np, sympy
from fractions import Fraction
from agg_scale import build_T, b_p
MA = int(sys.argv[1]); K = MA // 6 + 2
# prod (1-x^k)^4 = [prod(1-x^k)]^3 * prod(1-x^k); Jacobi: prod(1-x^k)^3 = sum_j (-1)^j (2j+1) x^{j(j+1)/2}; Euler: prod(1-x^k)=sum (-1)^j x^{j(3j-1)/2}
A = np.zeros(K + 1, dtype=object); B = np.zeros(K + 1, dtype=object)
j = 0
while j * (j + 1) // 2 <= K: A[j * (j + 1) // 2] += (-1) ** j * (2 * j + 1); j += 1
for j in range(-K, K + 1):
    e = j * (3 * j - 1) // 2
    if 0 <= e <= K: B[e] += (-1) ** (j % 2)
Ai = [int(a) for a in A]; Bi = [int(b) for b in B]
Bnz = [(e, b) for e, b in enumerate(Bi) if b]
poly = [0] * (K + 1)
for i, a in enumerate(Ai):
    if a:
        for e, b in Bnz:
            if i + e <= K: poly[i + e] += a * b
def c(n): return poly[(n - 1) // 6] if n % 6 == 1 else 0
T = build_T(2 * MA + 2)
sig = np.zeros(MA + 1, dtype=np.int64)
for d in range(1, MA + 1): sig[d::d] += d
bad = []; nz = 0; tot = 0; minr = (9, 0)
for m in range(1, MA + 1, 2):
    if m % 3 == 0: continue
    b = b_p(T, 2 * m, 3); s = int(sig[m]); tot += 1
    if 3 * b != 16 * (s - c(m)): bad.append(m)
    if c(m) != 0: nz += 1
    r = c(m) / s
    if r < minr[0]: minr = (r, m)
print(f"odd m<={MA}, 3 not | m: {tot} values tested, c(m)!=0 in {nz}; exceptions to b_3 = (16/3)(sigma - c): {len(bad)} {bad[:10]}")
print(f"min c(m)/sigma(m) = {minr[0]:.6f} at m={minr[1]}  (H31ndvd at p=3 needs >= -1/2)")
