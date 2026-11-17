# Brute-force test of the paper's Proposition 3.1:  b_p(n)/R(n) <= 2/(p(p-1)) + [p>3]*tau(m)*sqrt(m)/(3*sigma(m))
# for n=2m, m odd, all prime factors of m == 3 mod 4.  EMPIRICAL TEST, not a proof.
import numpy as np, math
from sympy import factorint, primerange
def tau_sigma(m):
    f=factorint(m); t=1; s=1
    for q,e in f.items(): t*=e+1; s*=(q**(e+1)-1)//(q-1)
    return t,s
def good_m(m):
    return m%2==1 and all(q%4==3 for q in factorint(m))
worst=(0,None); count=0; viol=[]; maxratio_total=(0,None)
for m in range(1,2400,2):
    if not good_m(m): continue
    n=2*m; B=int(math.isqrt(n))
    N=np.zeros(n+1,dtype=np.int64)       # opposite-parity pairs by norm
    xs=np.arange(-B,B+1)
    X,Y=np.meshgrid(xs,xs)
    nm=X*X+Y*Y; opp=((X+Y)%2==1)&(nm<=n)
    np.add.at(N,nm[opp],1)
    Rmix=int(sum(N[u]*N[n-u] for u in range(n+1)))
    t,s=tau_sigma(m)
    R=24*s
    assert Rmix*3==2*R, (m,Rmix,R)       # paper's (2.1),(2.2)
    tot=0
    for p in primerange(3,B+1):
        if p%4!=3: continue
        D=np.zeros(n+1,dtype=np.int64)
        dv=opp&(X%p==0)&(Y%p==0)
        np.add.at(D,nm[dv],1)
        bp=int(sum(D[u]*N[n-u]+N[u]*D[n-u]-D[u]*D[n-u] for u in range(n+1)))
        bound=2/(p*(p-1))+(1 if p>3 else 0)*t*math.sqrt(m)/(3*s)
        r=bp/R; count+=1
        if r>bound+1e-12: viol.append((m,p,r,bound))
        if r/bound>worst[0]: worst=(r/bound,(m,p,bp,R,r,bound))
    tot=None
print("(2.1)/(2.2) identities held for every tested m (assert).")
print("p-checks run:",count,"| violations of (3.1):",len(viol),viol[:3])
print("tightest case (ratio actual/bound):",worst)
