#!/usr/bin/env python3
"""Independent sieve check of the finite statement proved in EDcert*.lean (Euler 1747, n = 2 mod 4, n < 64^4):
every such n is a + b with a in the 43 EulerGood numbers 4i+1 <= 313 and b = n - a EulerGood (all prime factors = 1 mod 4).
Not part of the proof; a separate computation of the same statement."""
import numpy as np
N = 64 ** 4
good = np.ones(N, dtype=bool); good[0] = False
sieve = np.ones(N, dtype=bool); sieve[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if sieve[p]: sieve[p * p::p] = False
primes = np.nonzero(sieve)[0]
for p in primes:
    if p % 4 != 1: good[p::p] = False
cands = [a for a in range(1, 314) if a % 4 == 1 and good[a]]
assert len(cands) == 43 and cands[-1] == 313, (len(cands), cands[-1])
n = np.arange(2, N, 4)
cov = np.zeros(len(n), dtype=bool)
for a in cands:
    m = n > a
    cov[m] |= good[n[m] - a]
print("n = 2 mod 4 below 64^4:", len(n), " uncovered:", int((~cov).sum()))
