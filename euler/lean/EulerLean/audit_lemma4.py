# Numerical tests of Lemma 4.1 and Lemma 4.2 of Howe-Huffman-Kohlmeyer-Kruer (EMPIRICAL, not proofs).
import numpy as np, math
from sympy import factorint, primerange
# ---- Lemma 4.1: Nmix(t) <= 2(t+1), signed ordered pairs (x,y), opposite parity, x^2+y^2<=t
T=4000; B=int(math.isqrt(T)); xs=np.arange(-B,B+1); X,Y=np.meshgrid(xs,xs)
nm=X*X+Y*Y; opp=((X+Y)%2==1)&(nm<=T)
cnt=np.bincount(nm[opp],minlength=T+1); cum=np.cumsum(cnt)
viol=[t for t in range(0,T+1) if cum[t]>2*(t+1)]
print("Lemma 4.1: violations for integer t in [0,4000]:",viol[:5], "| max Nmix(t)/(2(t+1)) =",round(max(cum[t]/(2*(t+1)) for t in range(T+1)),4))
# ---- Lemma 4.2: (1/R) sum_{p>P} b_p <= (4/3) M(n) [ sum_{p>P} 1/p^2 + #{p in P3: P<p<=sqrt n}/n ]
def good_m(m): return m%2==1 and all(q%4==3 for q in factorint(m))
def Mfun(n):
    best=1
    for u in range(1,n+1):
        pr=1
        for q,e in factorint(u).items():
            if q%4==1: pr*=e+1
        best=max(best,pr)
    return best
P3all=[p for p in primerange(3,10**6) if p%4==3]
worst=0;viol2=[];tests=0
for m in range(1,1500,2):
    if not good_m(m): continue
    n=2*m; B=int(math.isqrt(n)); R=24*sum(d for d in range(1,m+1) if m%d==0)
    xs=np.arange(-B,B+1); X,Y=np.meshgrid(xs,xs); nm=X*X+Y*Y
    opp=((X+Y)%2==1)&(nm<=n); N=np.bincount(nm[opp],minlength=n+1).astype(np.int64)
    bps={}
    for p in P3all:
        if p>B: break
        D=np.bincount(nm[opp&(X%p==0)&(Y%p==0)],minlength=n+1).astype(np.int64)
        bps[p]=int(np.dot(D,N[::-1])+np.dot(N,D[::-1])-np.dot(D,D[::-1]))
    M=Mfun(n)
    for P in (3,5,7,11):
        lhs=sum(b for p,b in bps.items() if p>P)/R
        s2=sum(1/p**2 for p in P3all if p>P)
        cntp=sum(1 for p in P3all if P<p<=B)
        rhs=(4/3)*M*(s2+cntp/n)
        tests+=1
        if lhs>rhs+1e-12: viol2.append((m,P,lhs,rhs))
        worst=max(worst,lhs/rhs if rhs>0 else 0)
print("Lemma 4.2: tests",tests,"| violations",len(viol2),viol2[:3],"| worst lhs/rhs =",round(worst,3))
