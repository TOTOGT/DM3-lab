# Verifies the p-adic derivation by brute-force counting mod p^s (a check of the DERIVATION, run before any test of m).
# sigma(n)   = p^(-3s) #{x mod p^s : Q(x) = n mod p^s},  predicted (1-p^-2)(1+p^-1+...+p^-k)
# sigma_c(n) = same with p | x0, p | x1,                 predicted p^-2 (1+1/p)(1-p^-(k-1))   (k>=1)
# s >= k+2 so the counts have stabilised.
import numpy as np, itertools, sys
from fractions import Fraction as F
def counts(p, s):
    q = p ** s; c = np.zeros(q, dtype=np.int64); cc = np.zeros(q, dtype=np.int64)
    a = np.arange(q); w = (a[:, None] ** 2 + a[None, :] ** 2) % q
    np.add.at(c, w.ravel(), 1)
    a0 = np.arange(0, q, p); w0 = (a0[:, None] ** 2 + a0[None, :] ** 2) % q
    np.add.at(cc, w0.ravel(), 1)
    return c, cc, q
ok = True
for p, s, ks in [(3, 4, [1, 2]), (3, 5, [3]), (3, 6, [4]), (7, 3, [1]), (7, 4, [2]), (11, 3, [1]), (11, 4, [2]), (19, 3, [1, 2])]:
    c, cc, q = counts(p, s)
    for k in ks:
        n = (p ** k) % q
        # n = p^k * 5 mod q (a unit multiple) to avoid n = p^k only
        for unit in (1, 2, 5):
            nn = (p ** k * unit) % q
            if nn % p ** (k + 1) == 0 and k + 1 <= s - 2: continue
            tot = sum(int(c[w]) * int(c[(nn - w) % q]) for w in range(q) if c[w] and c[(nn - w) % q])
            con = sum(int(cc[w]) * int(c[(nn - w) % q]) for w in range(q) if cc[w] and c[(nn - w) % q])
            # constrained: x0,x1 in pZ (counted by cc over (x0,x1) mod q, i.e. multiples of p), x2,x3 free mod q
            sig = F(tot, q ** 3); sigc = F(con, q ** 3)
            ps = (1 - F(1, p * p)) * sum(F(1, p ** i) for i in range(k + 1))
            pc = F(1, p * p) * (1 + F(1, p)) * (1 - F(1, p ** (k - 1)))
            good = (sig == ps) and (sigc == pc)
            ok &= good
            print(f"p={p} s={s} k={k} unit={unit}: sigma={sig} (pred {ps})  sigma_c={sigc} (pred {pc})  {'OK' if good else 'MISMATCH'}")
print("ALL OK" if ok else "SOME MISMATCH")
