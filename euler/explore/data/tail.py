# Tail test: actual sum_{p>P} b_p(2m) vs M-based bound 16 M(n) sum_{p>P}(n/p^2+1), p = 3 mod 4, p <= sqrt(n), p does not divide m (and p | m too, all p). EVIDENCE ONLY.
import numpy as np, math
from sympy import factorint, primerange
MMAX=20000; NMAX=2*MMAX; B=math.isqrt(NMAX)
xs=np.arange(-B,B+1); X,Y=np.meshgrid(xs,xs); nm=X*X+Y*Y
opp=((X+Y)%2==1)&(nm<=NMAX)
N=np.bincount(nm[opp],minlength=NMAX+1).astype(np.int64)
r2=np.bincount(nm[nm<=NMAX],minlength=NMAX+1)
Mrun=np.maximum.accumulate(np.r_[0,r2[1:]])/4.0   # M(n)=max_{1<=u<=n} r2(u)/4
primes=[p for p in primerange(3,B+1) if p%4==3]
D={p:np.bincount(nm[opp&(X%p==0)&(Y%p==0)],minlength=NMAX+1).astype(np.int64) for p in primes}
def ts(m):
    f=factorint(m); s=1
    for q,e in f.items(): s*=(q**(e+1)-1)//(q-1)
    return s
out=[]
for m in range(1001,MMAX,2):
    if any(q%4!=3 for q in factorint(m)): continue
    n=2*m; s=ts(m); Rmix=16*s; M=Mrun[n]
    bp={}
    for p in primes:
        if p*p>n: break
        d=D[p][:n+1]; nn=N[:n+1]
        bp[p]=int(d@nn[::-1]+nn@d[::-1]-d@d[::-1])
    Pn=math.floor(2*n**0.25)
    while (Pn+1)**4<=16*n: Pn+=1
    while Pn**4>16*n: Pn-=1          # Lean Pn = floor(2 n^(1/4)), exact
    for P in (7, Pn):
        tail=sum(v for p,v in bp.items() if p>P)
        bound=16*M*sum(n/p**2+1 for p in bp if p>P)
        out.append((m,P==7,tail/Rmix,tail/bound if bound else 0, tail*P/n, M))
for flag,name in ((True,"P=7"),(False,"P=Pn=floor(2n^(1/4))")):
    r=[o for o in out if o[1]==flag]
    print(name,"m count",len(r),"| max tail/|Rmix|",round(max(o[2] for o in r),4),"| max tail/(M-bound)",round(max(o[3] for o in r),4),
          "| median tail/(M-bound)",round(float(np.median([o[3] for o in r])),4),"| max tail*P/n",round(max(o[4] for o in r),3))
    for lo,hi in [(1000,5000),(5000,10000),(10000,20000)]:
        rr=[o for o in r if lo<=o[0]<hi]
        print(f"   m in [{lo},{hi}): max tail*P/n={max(o[4] for o in rr):.3f}  max tail/Mbound={max(o[3] for o in rr):.4f}  M range {min(o[5] for o in rr)}-{max(o[5] for o in rr)}")
